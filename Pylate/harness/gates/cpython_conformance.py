#!/usr/bin/env python3
"""Check the rule interpreter against the CPython callable oracle.

Each concrete scenario in callable_rule_scenarios.json is executed in CPython
and analysed by pylate-rules as an admitted program. The soundness criterion
is inclusion: whatever CPython does at the call site must appear among the
abstract outcomes of that site.

    python3.13 tests/cpython_conformance.py            # summary + failures
    python3.13 tests/cpython_conformance.py --rule list.insert
    python3.13 tests/cpython_conformance.py --verbose

Exit status is non-zero when a scenario's CPython outcome is missing from the
abstract result, or when a scenario is not admitted by the checker.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import textwrap
import traceback

import sys as _sys, os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import paths
paths.on_path()
RULES = paths.PYLATE
SCENARIOS = paths.data("callable_rule_scenarios.json")
FUZZ = paths.data("callable_rule_fuzz.json")
SKIP = paths.data("cpython_conformance_skip.json")


def load_scenarios(path: str = SCENARIOS) -> list[dict]:
    with open(path, encoding="utf-8") as handle:
        return json.load(handle)["scenarios"]


def load_skips() -> dict[str, str]:
    """Scenarios deliberately outside the admitted fragment, with a reason."""
    if not os.path.exists(SKIP):
        return {}
    with open(SKIP, encoding="utf-8") as handle:
        return json.load(handle)["skip"]


# ------------------------------------------------------------------ CPython

def run_cpython(scenario: dict) -> dict:
    """Execute one scenario in a fresh namespace and record its outcome."""
    execution = scenario["execution"]
    events: list[str] = []
    namespace: dict[str, object] = {"events": events}
    setup = execution.get("setup") or ""
    try:
        exec(setup, namespace)  # noqa: S102 - corpus-declared setup
    except Exception as error:  # noqa: BLE001
        return {"kind": "setup-error", "type": type(error).__name__}
    try:
        value = eval(execution["call"], namespace)  # noqa: S307 - corpus call
    except Exception as error:  # noqa: BLE001
        return {
            "kind": "raise",
            "type": f"{type(error).__module__}.{type(error).__qualname__}",
            "events": events,
        }
    return {
        "kind": "return",
        "type": f"{type(value).__module__}.{type(value).__qualname__}",
        "events": events,
    }


# ------------------------------------------------------------------ analysis

def program_source(scenario: dict) -> tuple[str, int]:
    """The admitted program for a scenario, plus the 1-based call line.

    Setup runs at module level: the corpus declares hook classes there, and a
    class nested in a function is outside the admitted fragment.
    """
    execution = scenario["execution"]
    setup = execution.get("setup") or "pass"
    # `events.append(...)` is CPython-side instrumentation over a global list
    # the analysed program has no equivalent for; the line is replaced rather
    # than removed so the call line stays stable.
    def strip_instrumentation(line: str) -> str:
        body = line.lstrip()
        instrumentation = body.startswith("events.append(") or (
            "+=" in body and body.split("+=")[0].strip().isidentifier()
        ) or ("+=" in body and body.startswith("self."))
        if not instrumentation:
            return line
        return line[: len(line) - len(body)] + "pass"

    setup_lines = [
        strip_instrumentation(line) for line in setup.split("\n")
    ]
    call_line = len(setup_lines) + 1
    source = "\n".join(setup_lines) + f"\nresult = {execution['call']}\n"
    return source, call_line


def analyze(source: str, directory: str, name: str,
            policy: str = "audit") -> dict:
    path = os.path.join(directory, f"{name}.py")
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(source)
    # Whichever front end is active -- the Strata AST by default.
    ast_path = paths.make_analyzer_input(path, os.path.join(directory, name))
    log_path = os.path.join(directory, f"{name}.{policy}.log.json")
    subprocess.run(
        [RULES, ast_path, "--src", path, "--policy", policy, "-o", log_path],
        check=True,
        capture_output=True,
    )
    with open(log_path, encoding="utf-8") as handle:
        return json.load(handle)


# ------------------------------------------------------------------ matching

def site_rows(log: dict, line: int) -> list[dict]:
    return [
        residual
        for residual in log["residuals"].values()
        if residual["line"] == line
    ]


def abstract_outcomes(log: dict, line: int) -> tuple[set[str], bool, set[str]]:
    """(raised classes, a normal outcome exists, abort classes) at one line."""
    raised: set[str] = set()
    aborted: set[str] = set()
    normal = False
    for residual in site_rows(log, line):
        for error in residual["errors"]:
            _, _, outcome = error.partition(" -> ")
            outcome = outcome.strip()
            if outcome.startswith("abort "):
                aborted.add(outcome[len("abort "):])
            else:
                raised.add(outcome)
        if residual["cases"]:
            normal = True
        if residual["result"]["tags"]:
            normal = True
    for site in log.get("machine_raises", []):
        if site["line"] != line:
            continue
        if site["mode"] == "abort":
            aborted.add(site["exc"])
        else:
            raised.add(site["exc"])
    for obligation in log["obligations"]:
        if obligation["line"] == line and obligation["kind"] == "guaranteed-error":
            normal = False
    return raised, normal, aborted


def short(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def excess(log: dict, line: int, concrete: dict) -> str | None:
    """Outcomes the abstract result admits that this concrete input cannot take.

    Every scenario input is a literal, so CPython's single outcome is the only
    reachable one: anything else in the abstract result is over-approximation,
    justified or not.
    """
    raised, normal, aborted = abstract_outcomes(log, line)
    modelled = raised | aborted
    if concrete["kind"] == "raise":
        expected = short(concrete["type"])
        extra = sorted(c for c in modelled if c != expected)
        parts = []
        if normal:
            parts.append("normal")
        parts.extend(extra)
        if parts:
            return f"CPython raises {expected}; also admits {', '.join(parts)}"
        return None
    if modelled:
        return (
            f"CPython returns {short(concrete['type'])}; also admits "
            + ", ".join(sorted(modelled))
        )
    return None


def check(scenario: dict, log: dict, line: int, concrete: dict) -> str | None:
    raised, normal, aborted = abstract_outcomes(log, line)
    if not site_rows(log, line) and not any(
        site["line"] == line for site in log.get("machine_raises", [])
    ):
        return "no dispatch site recorded for the call"
    if concrete["kind"] == "raise":
        expected = short(concrete["type"])
        if expected in raised or expected in aborted:
            return None
        return (
            f"CPython raises {expected}; abstract raised="
            f"{sorted(raised) or '{}'} aborted={sorted(aborted) or '{}'}"
        )
    if not normal:
        return "CPython returns normally; abstract result has no normal outcome"
    return None


# ---------------------------------------------------------------------- main

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rule", action="append", dest="rules")
    parser.add_argument(
        "--corpus",
        default=SCENARIOS,
        help="scenario file to check (default: the hand-written corpus)",
    )
    parser.add_argument(
        "--fuzz",
        action="store_const",
        const=FUZZ,
        dest="corpus",
        help="check the generated fuzz corpus instead",
    )
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument(
        "--tight",
        action="store_true",
        help="report over-approximation instead of unsoundness",
    )
    parser.add_argument("--list-skipped", action="store_true")
    parser.add_argument(
        "--policy",
        action="append",
        dest="policies",
        choices=("strict", "eafp", "audit"),
        help="policy to check; repeat for several (default: all three)",
    )
    arguments = parser.parse_args()

    policies = tuple(arguments.policies or ("strict", "eafp", "audit"))
    skips = load_skips()
    scenarios = [s for s in load_scenarios(arguments.corpus) if "execution" in s]
    if arguments.rules:
        wanted = set(arguments.rules)
        scenarios = [s for s in scenarios if s["rule_key"] in wanted]

    failures: list[tuple[str, str]] = []
    rejected: list[tuple[str, str]] = []
    skipped: list[str] = []
    checked = 0
    disagreements: list[str] = []

    with tempfile.TemporaryDirectory(prefix="pylate-oracle-") as directory:
        for scenario in scenarios:
            identifier = scenario["id"]
            if identifier in skips:
                skipped.append(f"{identifier}: {skips[identifier]}")
                continue
            concrete = run_cpython(scenario)
            if concrete["kind"] == "setup-error":
                failures.append((identifier, f"setup failed: {concrete['type']}"))
                continue
            declared = scenario["expect"]["outcome"]
            if declared["kind"] != "generated" and (
                declared["kind"] != concrete["kind"]
                or short(declared.get("type", "")) != short(concrete["type"])
            ):
                disagreements.append(
                    f"{identifier}: corpus says {declared}, CPython says {concrete}"
                )
            source, line = program_source(scenario)
            for policy in policies:
                try:
                    log = analyze(source, directory, identifier, policy)
                except subprocess.CalledProcessError as error:
                    failures.append(
                        (identifier, f"analyzer failed under {policy}: {error}")
                    )
                    continue
                if log["status"] != "accepted":
                    rules = sorted({v["rule"] for v in log["violations"]})
                    rejected.append((identifier, ",".join(rules)))
                    break
                checked += 1
                problem = (
                    excess(log, line, concrete) if arguments.tight
                    else check(scenario, log, line, concrete)
                )
                if problem:
                    failures.append((identifier, f"[{policy}] {problem}"))
                elif arguments.verbose:
                    print(f"ok   {identifier} ({policy})")

    if arguments.list_skipped:
        for entry in skipped:
            print(f"skip {entry}")

    for identifier, reason in rejected:
        print(f"REJECTED {identifier}: {reason}")
    for identifier, reason in failures:
        print(f"{'LOOSE   ' if arguments.tight else 'UNSOUND '} {identifier}: {reason}")
    for entry in disagreements:
        print(f"CORPUS   {entry}")

    print(
        f"\nchecked={checked} unsound={len(failures)} "
        f"not-admitted={len(rejected)} skipped={len(skipped)} "
        f"corpus-drift={len(disagreements)}"
    )
    return 1 if failures or rejected or disagreements else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception:  # noqa: BLE001
        traceback.print_exc()
        sys.exit(2)
