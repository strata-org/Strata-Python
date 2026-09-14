#!/usr/bin/env python3
"""Measure where each rule loses precision, and to what.

The validity gate asks whether a rule's claim *contains* what CPython does. This
asks how much wider than CPython the claim is, and attributes each excess to the
static fact that would have settled it.

    python3.13 tests/rule_precision.py                 # the per-cause table
    python3.13 tests/rule_precision.py --by-rule       # per rule, worst first
    python3.13 tests/rule_precision.py --cause bounds  # the cases behind one

Three things are counted per case, all against the same corpus the validity gate
uses, so every number here is backed by a case that reaches the rule:

  obligations   a condition the domain could not settle, by kind
  excess-raise  a raise edge admitted that this input cannot take
  any-result    an operation whose result widened to `any`

`--tight` on the validity gate reports excess *bindings*; this reports excess
*outcomes*, which is what obligation counts are made of.
"""

from __future__ import annotations

import argparse
import collections
import concurrent.futures
import json
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rule_validity import (  # noqa: E402
    analyze, imported_names, inventory, load_cases, run_cpython, source_of,
)
import cpython_conformance  # noqa: E402


def every_case() -> list[dict]:
    """Both corpora, in this file's case shape.

    The validity corpus covers the syntax rules, the transfers, and `bytes`; the
    other 105 builtin rules live in the callable-rule corpus. Measuring only the
    first would report precision for 123 of 228 rules and say nothing about the
    ones most likely to be imprecise, so both are read here.
    """
    cases = list(load_cases())
    for scenario in cpython_conformance.load_scenarios():
        # 13 scenarios assert over abstract outcomes rather than one run. They
        # have no single concrete result to measure a width against, so they are
        # the validity gate's business and not this one's.
        if "execution" not in scenario:
            continue
        source, _ = cpython_conformance.program_source(scenario)
        # Take the recorded outcome rather than re-running the scenario. Its
        # setups instrument through an `events` list this harness does not
        # supply, and `cpython_conformance.py` already validates every recorded
        # outcome against live CPython on each run -- that is its
        # `corpus-drift=0` -- so the record is a gated fact, not a stale note.
        outcome = scenario.get("expect", {}).get("outcome", {})
        if outcome.get("kind") not in ("return", "raise"):
            continue
        cases.append({"rule": scenario["rule_key"],
                      "name": scenario["scenario"],
                      "source": source,
                      "outcome": outcome})
    return cases

#: What each obligation kind is waiting on. The right column names the static
#: fact that would discharge it, which is what makes this a domain shopping list
#: rather than a complaint.
WANTS: dict[str, str] = {
    "unreported-outcome": "an outcome the rule declares but no site reported",
    "key-membership": "whether a key is in a dict",
    "assert": "whether an asserted condition holds",
    "default-arg": "a default argument's value",
    "bounds": "an index and a container length",
    "index": "an index and a container length",
    "unpack-arity": "a container length",
    "key": "a dict key set",
    "arith": "whether a divisor is zero",
    "value": "a literal value",
    "dispatch-any": "the type of an unknown value",
    "deferred-dispatch": "the type of an operand",
    "special-method": "the element type of a protocol iterator",
    "method-escape": "a bound method as a first-class value",
    "attr-missing": "a field outside the declared layout",
    "uninit-field": "whether a field was assigned on every path",
    "error-guard": "whether a guarded operation can fail",
    "guaranteed-error": "nothing: the analyzer is certain",
    "contract": "an argument's type at the call",
    "return-annotation": "a returned value's type",
    "raised-class": "which class a raise carries",
    "raise-point-state": "the state at a raise",
    "shape-break": "a TypedDict's key set after a write",
    "case-split": "which of several targets a call reaches",
    "proof-boundary": "a recursive annotation",
    "subterm-index": "a plan/node mismatch (a bug, not imprecision)",
    "syntax-rule-missing": "a missing plan (a bug, not imprecision)",
}


def measure(case: dict) -> dict:
    source = source_of(case)
    ident = f"{case['rule'].replace(':', '_').replace('.', '_')}_{case['name']}"
    try:
        if "outcome" in case:
            kind = case["outcome"]["kind"]
            concrete = {"kind": kind, "lines": [],
                        "type": case["outcome"].get("type", "").rsplit(".", 1)[-1],
                        "bindings": {}}
        else:
            concrete = run_cpython(source)
        with tempfile.TemporaryDirectory() as directory:
            log = analyze(source, directory, ident)
    except Exception as error:  # noqa: BLE001
        return {"rule": case["rule"], "name": case["name"],
                "error": repr(error)}
    if log["status"] != "accepted":
        return {"rule": case["rule"], "name": case["name"], "rejected": True}

    obligations = collections.Counter(o["kind"] for o in log["obligations"])

    # A raise edge this input cannot take. CPython took exactly one outcome, so
    # anything else at that site is width.
    took = concrete["type"] if concrete["kind"] == "raise" else None
    excess: list[str] = []
    anyresult: list[str] = []
    for residual in log["residuals"].values():
        # Attribute the edge to the operation that produced it, not to the rule
        # the case is named for. Every bytes case builds its receiver with
        # `str.encode`, so charging that operation's edges to `bytes.partition`
        # made the whole bytes family look imprecise and hid the one rule that
        # actually is.
        where = residual["desc"] or residual["kind"]
        for error in residual["errors"]:
            _, _, outcome = error.partition(" -> ")
            outcome = outcome.strip().removeprefix("abort ")
            if outcome != took:
                excess.append(f"{where} -> {outcome}")
        if "any" in residual["result"]["tags"]:
            anyresult.append(where)

    # A binding wider than the value CPython left there.
    skip = imported_names(source)
    widened = 0
    if concrete["kind"] == "return" and log["lines"]:
        last = max(log["lines"], key=int)
        env = log["lines"][last]["env"]
        for name in concrete["bindings"]:
            if name in skip or name not in env:
                continue
            if len(env[name]["tags"]) > 1:
                widened += 1

    return {
        "rule": case["rule"],
        "name": case["name"],
        "obligations": dict(obligations),
        "excess": excess,
        "anyresult": anyresult,
        "widened": widened,
        "sites": len(log["residuals"]),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--by-rule", action="store_true")
    parser.add_argument("--cause")
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    args = parser.parse_args()

    cases = every_case()
    items = inventory()
    with concurrent.futures.ProcessPoolExecutor(args.jobs) as pool:
        results = [r for r in pool.map(measure, cases)]

    live = [r for r in results if "obligations" in r]
    print(f"{len(live)} admitted cases over {len(items)} rules "
          f"({len(results) - len(live)} rejected-by-design or errored)\n")

    if args.cause:
        rows = [r for r in live if args.cause in r["obligations"]]
        print(f"{len(rows)} cases raise `{args.cause}`"
              f" — wants {WANTS.get(args.cause, '?')}\n")
        for row in sorted(rows, key=lambda r: -r["obligations"][args.cause]):
            print(f"  {row['obligations'][args.cause]:3d}  "
                  f"{row['rule']} / {row['name']}")
        return 0

    if args.by_rule:
        per: dict[str, dict] = {}
        for row in live:
            entry = per.setdefault(row["rule"], {"obl": 0, "excess": 0,
                                                 "any": 0, "wide": 0, "n": 0})
            entry["obl"] += sum(row["obligations"].values())
            entry["excess"] += len(row["excess"])
            entry["any"] += len(row["anyresult"])
            entry["wide"] += row["widened"]
            entry["n"] += 1
        print(f"{'rule':44s} {'obl':>4s} {'raise':>6s} {'any':>4s} "
              f"{'wide':>5s}  cases")
        for rule, entry in sorted(
                per.items(),
                key=lambda kv: -(kv[1]["obl"] + kv[1]["excess"]
                                 + kv[1]["any"] * 2)):
            if not (entry["obl"] or entry["excess"] or entry["any"]
                    or entry["wide"]):
                continue
            print(f"{rule:44s} {entry['obl']:4d} {entry['excess']:6d} "
                  f"{entry['any']:4d} {entry['wide']:5d}  {entry['n']}")
        clean = [r for r, e in per.items()
                 if not (e["obl"] or e["excess"] or e["any"] or e["wide"])]
        print(f"\n{len(clean)} rules are exact on every case they have.")
        return 0

    kinds: collections.Counter = collections.Counter()
    rules_per_kind: dict[str, set[str]] = collections.defaultdict(set)
    for row in live:
        for kind, count in row["obligations"].items():
            kinds[kind] += count
            rules_per_kind[kind].add(row["rule"])
    print(f"{'obligation':22s} {'count':>6s} {'rules':>6s}  "
          f"wants")
    for kind, count in kinds.most_common():
        print(f"{kind:22s} {count:6d} {len(rules_per_kind[kind]):6d}  "
              f"{WANTS.get(kind, '(unclassified)')}")

    excess: collections.Counter = collections.Counter()
    for row in live:
        excess.update(row["excess"])
    print(f"\nexcess raise edges by operation ({sum(excess.values())} total, "
          f"top 18 of {len(excess)}):")
    for edge, count in excess.most_common(18):
        print(f"  {count:4d}  {edge}")

    anys: collections.Counter = collections.Counter()
    for row in live:
        anys.update(row["anyresult"])
    print(f"\nresults widened to `any` ({sum(anys.values())} total):")
    for kind, count in anys.most_common():
        print(f"  {count:4d}  {kind}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
