#!/usr/bin/env python3
"""Check every rule of the abstract interpreter against the CPython runtime.

A rule is *valid* when what CPython actually does on the construct it governs is
contained in what the rule claims. This gate asserts that containment, one rule
at a time, and refuses to pass while any rule has no case at all.

Each case is a whole admitted module. The gate runs it twice -- once under this
interpreter, once under the analyzer -- and compares:

  raised    the class CPython raised must appear among the outcomes the analyzer
            records at the raising line, which the traceback supplies
  bindings  every module-level name CPython left bound must carry a tag that
            covers the value's runtime type
  reached   a module that completes normally must have a normal completion in
            the analyzer, and every line CPython executed must be reachable

The direction is the only one that matters. The analyzer may admit outcomes
CPython did not take on this input; it may not miss one CPython took. Use
`--tight` to see the over-approximation instead.

The rule inventory comes from `pylate --dump-rules`, and the transfer inventory
from the `CLAIM:` markers in `Pylate/Transfers/*.lean`, so neither can drift into
agreement with this file's idea of what exists.

    python3.13 tests/rule_validity.py               # every case, then coverage
    python3.13 tests/rule_validity.py --rule expr:binop
    python3.13 tests/rule_validity.py --coverage     # what has no case yet
    python3.13 tests/rule_validity.py --verbose
"""

from __future__ import annotations

import argparse
import ast
import concurrent.futures
import json
import os
import re
import subprocess
import sys
import tempfile
import traceback

import sys as _sys, os as _os
_sys.path.insert(0, _os.path.dirname(_os.path.dirname(_os.path.abspath(__file__))))
import paths
paths.on_path()
PYLATE = paths.PYLATE
TRANSFERS = paths.TRANSFERS
CASES = paths.data("rule_validity_cases.json")
#: The older callable-rule corpus. It validates its rules against CPython by the
#: same containment criterion, so it counts for coverage and its rules are not
#: re-authored here; `cpython_conformance.py` is what runs it.
CONFORMANCE = paths.data("callable_rule_scenarios.json")

#: A runtime type, as `type(value).__name__`, and the tag that covers it. A type
#: absent here is reported rather than skipped: it means the case produced a
#: value the domain has no tag for, which is worth seeing.
TYPE_TAG: dict[str, str] = {
    "NoneType": "none",
    "bool": "bool",
    "int": "int",
    "float": "float",
    "complex": "complex",
    "str": "str",
    "bytes": "bytes",
    "list": "list",
    "dict": "dict",
    "set": "set",
    "tuple": "tuple",
    "range": "range",
    "dict_keys": "dict_keys",
    "dict_items": "dict_items",
    "dict_values": "dict_values",
    "generator": "gen",
    "function": "func",
    "type": "type",
    "NotImplementedType": "NotImplemented",
}


# ------------------------------------------------------------------ inventory

def declared_rules() -> list[tuple[str, str]]:
    """`(kind, key)` for every rule in the two rule sets, from the binary."""
    out = subprocess.run(
        [PYLATE, "--dump-rules"], capture_output=True, text=True, check=True
    ).stdout
    rules = []
    for line in out.splitlines():
        if not line.strip():
            continue
        kind, _, key = line.partition("\t")
        rules.append((kind, key))
    return rules


CLAIM = re.compile(r"CLAIM\s+([a-z0-9][a-z0-9-]*):")


def transfer_claims() -> dict[str, str]:
    """`claim id -> file` for every `CLAIM:` marker under `Transfers/`.

    The transfers are hand-written, so they have no rule table to enumerate.
    Each observable step carries a marker in its docstring instead, and this gate
    requires a case per marker -- which is what makes an unclaimed new protocol
    step visible rather than silently untested.
    """
    claims: dict[str, str] = {}
    for name in sorted(os.listdir(TRANSFERS)):
        if not name.endswith(".lean"):
            continue
        path = os.path.join(TRANSFERS, name)
        with open(path, encoding="utf-8") as handle:
            for match in CLAIM.finditer(handle.read()):
                claims[f"transfer:{match.group(1)}"] = name
    return claims


def inventory() -> dict[str, str]:
    """Everything that needs a case: `key -> kind`."""
    items = {key: kind for kind, key in declared_rules()}
    items.update({key: "transfer" for key in transfer_claims()})
    return items


def load_cases() -> list[dict]:
    with open(CASES, encoding="utf-8") as handle:
        return json.load(handle)["cases"]


def conformance_rules() -> set[str]:
    """Rules the callable-rule corpus already validates against CPython."""
    if not os.path.exists(CONFORMANCE):
        return set()
    with open(CONFORMANCE, encoding="utf-8") as handle:
        return {s["rule_key"] for s in json.load(handle)["scenarios"]}


# -------------------------------------------------------------------- CPython

def run_cpython(source: str) -> dict:
    """Execute a case and record what this interpreter did.

    `lines` is every source line the case actually reached, collected by a trace
    function: a case whose interesting branch never ran is a case that proves
    nothing, and the analyzer's reachability claim is checkable against it.
    """
    executed: set[int] = set()
    filename = "<case>"

    def tracer(frame, event, arg):  # noqa: ANN001
        if frame.f_code.co_filename == filename:
            if event == "line":
                executed.add(frame.f_lineno)
            return tracer
        return None

    namespace: dict[str, object] = {"__name__": "case"}
    code = compile(source, filename, "exec")
    sys.settrace(tracer)
    try:
        exec(code, namespace)  # noqa: S102 - the case corpus is the input
    except BaseException as error:  # noqa: BLE001 - any outcome is data here
        sys.settrace(None)
        line = None
        for frame, lineno in traceback.walk_tb(error.__traceback__):
            if frame.f_code.co_filename == filename:
                line = lineno
        return {
            "kind": "raise",
            "type": type(error).__name__,
            "line": line,
            "lines": sorted(executed),
        }
    finally:
        sys.settrace(None)
    bindings = {}
    for name, value in namespace.items():
        if name.startswith("__"):
            continue
        kind = type(value).__name__
        if isinstance(value, type):
            kind = "type"
        bindings[name] = kind
    return {"kind": "return", "bindings": bindings, "lines": sorted(executed)}


# ------------------------------------------------------------------- analyzer

def analyze(source: str, directory: str, name: str) -> dict:
    path = os.path.join(directory, f"{name}.py")
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(source)
    # Whichever front end is active -- the Strata AST by default.
    ast_path = paths.make_analyzer_input(path, os.path.join(directory, name))
    log_path = os.path.join(directory, f"{name}.log.json")
    subprocess.run(
        [PYLATE, ast_path, "--src", path, "--policy", "audit", "-o", log_path],
        check=True,
        capture_output=True,
    )
    with open(log_path, encoding="utf-8") as handle:
        return json.load(handle)


def outcomes_at(log: dict, line: int) -> tuple[set[str], bool]:
    """`(classes the analyzer says may escape here, a normal outcome exists)`."""
    raised: set[str] = set()
    normal = False
    for residual in log["residuals"].values():
        if residual["line"] != line:
            continue
        for error in residual["errors"]:
            _, _, outcome = error.partition(" -> ")
            outcome = outcome.strip()
            raised.add(outcome[len("abort "):] if outcome.startswith("abort ")
                       else outcome)
        if residual["cases"] or residual["result"]["tags"]:
            normal = True
    for site in log.get("machine_raises", []):
        if site["line"] == line:
            raised.add(site["exc"])
    return raised, normal


def claimed_tags(log: dict, name: str) -> set[str] | None:
    """The tags the analyzer gives `name` at the end of the module.

    `lines[n].env` is the state *before* line n, so the case sources end in a
    trailing statement the gate appends and the last entry is the final state.
    """
    if not log["lines"]:
        return None
    last = max(log["lines"], key=int)
    entry = log["lines"][last]["env"].get(name)
    if entry is None:
        return None
    tags = set(entry["tags"])
    if entry["funcs"]:
        tags.add("func")
    if entry["classes"]:
        tags.add("type")
    return tags


def static_binding(log: dict, name: str, runtime: str) -> bool:
    """Is this name a static binding rather than a value in the environment?

    A module-level `def` or `class` is resolved by name in this design -- the
    class table answers for a class, devirtualization for a function -- so
    neither appears in `env`. A class is still checked, against the class table.
    A function is not: what the analyzer claims about it is the dispatch target,
    which the site checks and the callable-rule corpus assert instead.
    """
    if runtime == "type":
        return name in log.get("resolution", {}).get("classes", {})
    return runtime == "function"


# -------------------------------------------------------------------- compare

def covers(tags: set[str], runtime: str) -> bool:
    """Does a claimed tag set cover a value of this runtime type?"""
    if "any" in tags:
        return True
    # A type the table does not name is an instance of a user class, which the
    # domain tags by class name. Matching any `obj:` would pass a case that got
    # the class wrong, so this stays exact.
    tag = TYPE_TAG.get(runtime, f"obj:{runtime}")
    return tag in tags


def imported_names(source: str) -> set[str]:
    """Names an `import` binds.

    CPython binds them in the module namespace; the analyzer reads an import for
    its annotation vocabulary and does not give the name a value. Comparing them
    would only measure that difference.
    """
    names: set[str] = set()
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                names.add(alias.asname or alias.name.split(".")[0])
    return names


def check(case: dict, source: str, log: dict, concrete: dict) -> list[str]:
    """Every way this case's CPython outcome escapes the analyzer's claim."""
    problems: list[str] = []
    rejected = log["status"] != "accepted"
    if case.get("expect") == "rejected":
        if rejected:
            return []
        return ["the case documents a construct outside the subset, but the "
                "checker admitted it"]
    if rejected:
        reasons = [v.get("detail", v) for v in log.get("violations", [])][:2]
        return [f"not admitted by the subset checker: {reasons}"]
    skip = imported_names(source)

    if concrete["kind"] == "raise":
        line = concrete["line"]
        if line is None:
            return [f"CPython raised {concrete['type']} with no line in the case"]
        raised, _ = outcomes_at(log, line)
        module_wide = set(log.get("module", {}).get("may_raise", []))
        if concrete["type"] not in raised | module_wide:
            problems.append(
                f"CPython raises {concrete['type']} at line {line}; analyzer "
                f"has {sorted(raised) or '{}'} there, "
                f"module-wide {sorted(module_wide) or '{}'}"
            )
    else:
        for name, runtime in sorted(concrete["bindings"].items()):
            if name in skip:
                continue
            tags = claimed_tags(log, name)
            if tags is None:
                if static_binding(log, name, runtime):
                    continue
                problems.append(
                    f"CPython leaves `{name}` bound to a {runtime}; the "
                    "analyzer's final environment has no entry for it"
                )
                continue
            if not covers(tags, runtime):
                problems.append(
                    f"`{name}` is a {runtime} at runtime; analyzer claims "
                    f"{sorted(tags)}"
                )

    unreached = set(log.get("module", {}).get("unreached", []))
    ran = set(concrete["lines"])
    both = sorted(unreached & ran)
    if both:
        problems.append(
            f"analyzer calls line(s) {both} unreachable; CPython executed them"
        )
    return problems


def loose(case: dict, log: dict, concrete: dict) -> list[str]:
    """Outcomes the analyzer admits that this input cannot take. Not soundness."""
    if log["status"] != "accepted" or concrete["kind"] != "return":
        return []
    notes = []
    for name, runtime in sorted(concrete["bindings"].items()):
        tags = claimed_tags(log, name) or set()
        tag = TYPE_TAG.get(runtime, f"obj:{runtime}")
        extra = sorted(tags - {tag})
        if extra:
            notes.append(f"`{name}` is a {runtime}; also admits {extra}")
    return notes


# ----------------------------------------------------------------------- main

def source_of(case: dict) -> str:
    """The case body plus the trailing statement that exposes the final state."""
    body = case["source"]
    if not body.endswith("\n"):
        body += "\n"
    return body + "pass\n"


def too_old(case: dict) -> str | None:
    """Why this interpreter cannot run the case, if it cannot.

    A case may need a newer `typing` than the host provides -- `ReadOnly` is
    3.13 -- and executing it there raises `ImportError` before reaching the rule.
    That is reported as a skip rather than an unsound result, and counted, so the
    coverage figure cannot claim a rule is exercised here when it is not.
    """
    need = case.get("min_python")
    if need and tuple(sys.version_info[:len(need)]) < tuple(need):
        want = ".".join(str(n) for n in need)
        have = ".".join(str(n) for n in sys.version_info[:2])
        return f"needs Python {want}, running {have}"
    return None


def run_case(case: dict) -> dict:
    if (reason := too_old(case)) is not None:
        return {"case": case, "problems": [], "notes": [], "concrete": {},
                "skipped": reason}
    source = source_of(case)
    ident = f"{case['rule'].replace(':', '_').replace('.', '_')}_{case['name']}"
    try:
        concrete = run_cpython(source)
        with tempfile.TemporaryDirectory() as directory:
            log = analyze(source, directory, ident)
    except Exception as error:  # noqa: BLE001
        return {"case": case, "problems": [f"harness error: {error!r}"],
                "notes": [], "concrete": {}}
    return {
        "case": case,
        "problems": check(case, source, log, concrete),
        "notes": loose(case, log, concrete),
        "concrete": concrete,
    }


def report_coverage(items: dict[str, str], cases: list[dict]) -> int:
    here = {case["rule"] for case in cases}
    elsewhere = conformance_rules()
    covered = here | elsewhere
    stray = sorted(covered - set(items))
    missing_by_kind: dict[str, list[str]] = {}
    for key, kind in items.items():
        if key not in covered:
            missing_by_kind.setdefault(kind, []).append(key)
    total_missing = sum(len(v) for v in missing_by_kind.values())
    for kind in sorted(set(items.values())):
        keys = [k for k, v in items.items() if v == kind]
        mine = sum(1 for k in keys if k in here)
        theirs = sum(1 for k in keys if k in elsewhere and k not in here)
        print(f"  {kind:9s} {mine + theirs:3d}/{len(keys):3d} rules with a case"
              f"  ({mine} here, {theirs} in the callable-rule corpus)")
    for kind, keys in sorted(missing_by_kind.items()):
        print(f"\n  {kind} rules with no case ({len(keys)}):")
        for key in sorted(keys):
            print(f"    {key}")
    if stray:
        print(f"\n  cases naming no declared rule ({len(stray)}):")
        for key in stray:
            print(f"    {key}")
    return total_missing + len(stray)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rule", action="append", dest="rules")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument("--tight", action="store_true",
                        help="report over-approximation instead of unsoundness")
    parser.add_argument("--coverage", action="store_true",
                        help="only report which rules have no case")
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    args = parser.parse_args()

    items = inventory()
    cases = load_cases()
    if args.coverage:
        print(f"{len(cases)} cases over {len(items)} rules")
        return 1 if report_coverage(items, cases) else 0

    selected = cases
    if args.rules:
        selected = [c for c in cases if c["rule"] in set(args.rules)]
        if not selected:
            print(f"no case for {args.rules}", file=sys.stderr)
            return 2

    failures, notes, skipped = [], [], []
    with concurrent.futures.ProcessPoolExecutor(args.jobs) as pool:
        for result in pool.map(run_case, selected):
            case = result["case"]
            label = f"{case['rule']} / {case['name']}"
            if result.get("skipped"):
                skipped.append((label, result["skipped"], case["rule"]))
                print(f"skip    {label} ({result['skipped']})")
            elif result["problems"]:
                failures.append((label, result["problems"]))
                print(f"UNSOUND {label}")
                for problem in result["problems"]:
                    print(f"        {problem}")
            elif args.verbose:
                kind = result["concrete"].get("kind", "?")
                print(f"ok      {label} ({kind})")
            if result["notes"]:
                notes.append((label, result["notes"]))

    print(f"\n{len(selected)} cases, {len(failures)} unsound"
          + (f", {len(skipped)} skipped on this interpreter" if skipped else ""))
    if args.tight:
        print(f"{len(notes)} cases over-approximate:")
        for label, entries in notes:
            for note in entries:
                print(f"  {label}: {note}")

    if not args.rules:
        print("\ncoverage:")
        # A rule whose only case was skipped has a case but was not exercised
        # here; say so rather than counting it as covered without qualification.
        unexercised = sorted({rule for _, _, rule in skipped}
                             - {c["rule"] for c in selected
                                if not c.get("min_python")})
        if unexercised:
            print(f"  not exercised on this interpreter: "
                  f"{', '.join(unexercised)}")
        uncovered = report_coverage(items, cases)
        if uncovered:
            print(f"\n{uncovered} rules have no validity case")
            return 1
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
