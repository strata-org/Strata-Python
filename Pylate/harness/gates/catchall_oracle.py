"""Probe every (receiver tag, operation) pair against CPython.

The transfers for the operator protocols -- subscript, attribute, length,
iteration -- are hand-written Lean, and each ends in a catch-all arm that
*asserts* an exception for every tag it does not handle explicitly. That is a
claim, not a safe default. Asserting "only TypeError" where CPython returns a
value deletes the normal completion, and a deleted normal completion makes the
following statements unreachable, so their obligations discharge for free. It is
the `list.append` vacuity failure wearing a different hat.

Two holes were found by hand in `itemRead` this way: `bytes` is subscriptable and
yields an int, and subscripting a type builds a generic alias. Both fell into the
catch-all and were reported as always raising.

Two invariants, in opposite directions:

    1. if CPython completes normally, the analyzer must admit a normal completion
    2. if CPython raises E, the analyzer must report E as possible

The first is the one that matters most -- a deleted normal completion makes the
following code unreachable, so its obligations discharge for free. But the second
is not merely precision, because the tool's product is which exceptions escape: a
missing exception is a wrong answer to the question being asked.

The second was added after a defect the first could not see. `("a", 1)[s]` for a
string `s` reported `IndexError` and no `TypeError`, where CPython raises
`TypeError` and never `IndexError` -- wrong in both directions at once, and
invisible to invariant 1 because CPython does not complete normally there.

What is still not checked is an *extra* exception, which stays a precision cost
rather than a defect.

Run: python3.13 tests/catchall_oracle.py [--verbose]
"""
from __future__ import annotations

import concurrent.futures
import copy
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
PIPELINE = paths.PIPELINE

#: How to obtain a value of each tag inside an *admitted* program, and the
#: concrete CPython value to probe with. A tag whose values cannot be built in
#: the subset is skipped with its reason rather than silently dropped: bytes
#: literals are rejected, so bytes arrives through `str.encode`.
TAGS: dict[str, tuple[str, str, object]] = {
    # tag:        (parameter annotation, expression yielding it, CPython sample)
    "bool":       ("flag: bool", "flag", True),
    "int":        ("n: int", "n", 1),
    "float":      ("f: float", "f", 1.0),
    "str":        ("s: str", "s", "ab"),
    "bytes":      ("s: str", "s.encode()", b"ab"),
    "list":       ("xs: list[int]", "xs", [1, 2]),
    "dict":       ("d: dict[str, int]", "d", {"a": 1}),
    "set":        ("st: set[int]", "st", {1}),
    "tuple":      ("t: tuple[int, str]", "t", (1, "a")),
    "range":      ("n: int", "range(n)", range(3)),
    "none":       ("n: int", "None", None),
}

#: Each operation: how to write it in Python given a receiver expression, and how
#: to evaluate it on the CPython sample.
OPERATIONS: dict[str, tuple[str, object]] = {
    "subscript-int": ("{recv}[0]", lambda v: v[0]),
    "subscript-str": ('{recv}["k"]', lambda v: v["k"]),
    "length":        ("len({recv})", len),
    "truth":         ("1 if {recv} else 0", lambda v: 1 if v else 0),
    # `attributeRead` and `itemWrite` have their own catch-alls, and so do the
    # binary and comparison transfers. A store is not an expression, so it is
    # probed by mutating and then reading a witness back: if the write raised,
    # nothing reaches `probed`.
    "attr-real":     ("{recv}.real", lambda v: v.real),
    "attr-absent":   ("{recv}.nosuch", lambda v: v.nosuch),
    "store-int":     ("_store_int({recv})", lambda v: _store(v, 0, 1)),
    "store-str":     ("_store_str({recv})", lambda v: _store(v, "k", 1)),
    "add-int":       ("{recv} + 1", lambda v: v + 1),
    "add-str":       ('{recv} + "a"', lambda v: v + "a"),
    "add-self":      ("{recv} + {recv}", lambda v: v + v),
    "lt-int":        ("1 if {recv} < 1 else 0", lambda v: 1 if v < 1 else 0),
    "eq-int":        ("1 if {recv} == 1 else 0", lambda v: 1 if v == 1 else 0),
    "in-int":        ("1 if 1 in {recv} else 0", lambda v: 1 if 1 in v else 0),
}

#: Store probes need a statement, so their Python form is a helper the harness
#: emits rather than an expression substituted into a template.
STORE_HELPERS: dict[str, str] = {
    "_store_int": "    target[0] = 1\n    return target[0]\n",
    "_store_str": '    target["k"] = 1\n    return target["k"]\n',
}


def _store(sample, key, value):
    """CPython's answer for a store probe: assign, then read the slot back."""
    sample[key] = value
    return sample[key]


def _superclasses(name: str) -> list[str]:
    """The exception classes a report of `name` may legitimately be widened to."""
    cls = getattr(__builtins__, name, None) if not isinstance(__builtins__, dict) \
        else __builtins__.get(name)
    if not isinstance(cls, type):
        return []
    return [base.__name__ for base in cls.__mro__[1:] if base is not object]


def cpython_outcome(sample, evaluate) -> str:
    """`normal` when a value comes back, otherwise the exception's class name."""
    try:
        evaluate(sample)
        return "normal"
    except Exception as error:  # noqa: BLE001 - the class name is the answer
        return type(error).__name__


def probe_one(job: tuple) -> tuple:
    """One (tag, operation) pair: CPython's answer and the analyzer's.

    A module-level function taking only strings, because a pool pickles both.
    The tables hold lambdas, which do not pickle, so the worker looks the pair up
    by key -- the tables are module-level and so already present after import.
    """
    tag, operation = job
    annotation, expression, sample = TAGS[tag]
    template, evaluate = OPERATIONS[operation]
    # The store probes assign into the sample, and the samples are module-level
    # constants. Run serially, an earlier `d[0] = 1` left the key behind and a
    # later `d["k"]` probe found a dict it had never been given -- so two probes
    # disagreed about CPython depending on the order they ran in. A pool hides
    # that by giving each worker its own copy; copying here means the answer does
    # not depend on being parallel.
    sample = copy.deepcopy(sample)
    expected = cpython_outcome(sample, evaluate)
    body = template.format(recv=expression)
    helper = next((h for h in STORE_HELPERS if h in body), None)
    preamble = ""
    if helper is not None:
        _, kind = annotation.split(":", 1)
        preamble = (f"def {helper}(target:{kind}) -> object:\n"
                    f"{STORE_HELPERS[helper]}\n\n")
    source = (f"{preamble}"
              f"def probe({annotation}) -> object:\n"
              f"    probed = {body}\n"
              f"    return probed\n")
    log = analyze(source)
    return (tag, operation, expected, body,
            analyzer_admits_normal(log), analyzer_raises(log))


def analyze(source: str) -> dict | None:
    with tempfile.TemporaryDirectory() as work:
        path = os.path.join(work, "probe.py")
        with open(path, "w") as handle:
            handle.write(source)
        run = subprocess.run(
            [sys.executable, PIPELINE, path, "--logs-only", "--policy", "audit",
             "-o", os.path.join(work, "out.html")],
            capture_output=True, text=True)
        log_path = os.path.join(work, "probe.log.json")
        if run.returncode != 0 or not os.path.exists(log_path):
            return None
        with open(log_path) as handle:
            return json.load(handle)


def analyzer_raises(log: dict) -> set[str] | None:
    """Every exception class the analyzer reports for the probed program.

    Read from `machine_raises` rather than from a site's rows, because an abort
    and a modelled raise are both reports -- the policy decides whether execution
    continues, not whether the exception was found. The probe runs under `audit`,
    where everything is modelled, so both appear.
    """
    if log is None or log.get("status") != "accepted":
        return None
    return {entry["exc"] for entry in (log.get("machine_raises") or [])}


def analyzer_admits_normal(log: dict) -> bool | None:
    """Whether the probe's binding received a value.

    The probe binds the operation's result to `probed` and returns it, so the
    entry state of the `return` line answers the question directly: a non-bottom
    binding means a normal completion is admitted. Reading a *site's* result does
    not work uniformly -- a `truth` site legitimately carries bottom, because a
    truth test partitions the state rather than producing a value, and the value
    belongs to the enclosing conditional. Checking the binding sidesteps the
    question of which site owns the result.

    None when the program was rejected or the binding never appears, which the
    caller reports as a skip rather than as a pass.
    """
    if log is None or log.get("status") != "accepted":
        return None
    for state in (log.get("lines") or {}).values():
        binding = (state.get("env") or {}).get("probed")
        if binding is None:
            continue
        if binding["tags"] or binding["locs"]:
            return True
    return False


def main() -> int:
    verbose = "--verbose" in sys.argv
    failures: list[str] = []
    skips: list[str] = []
    checked = 0
    #: How many pairs each invariant actually decided. Printed because a check
    #: that never runs reports zero failures exactly like one that passes.
    normal_checked = 0
    raise_checked = 0

    jobs = [(tag, operation) for tag in sorted(TAGS)
            for operation in sorted(OPERATIONS)]

    # Independent probes, one per core: each writes its own temp dir and reads
    # only CPython. Serially this was almost entirely process startup.
    with concurrent.futures.ProcessPoolExecutor(
            max_workers=min(len(jobs), os.cpu_count() or 1)) as pool:
        outcomes = list(pool.map(probe_one, jobs))

    for (tag, operation, expected, body, admits, reported) in outcomes:
        checked += 1
        if admits is None:
            skips.append(f"{tag}/{operation}: no site produced "
                         f"(rejected or not modelled as a site)")
            continue
        if expected == "normal":
            normal_checked += 1
        else:
            raise_checked += 1
        if expected == "normal" and not admits:
            failures.append(
                f"{tag}/{operation}: CPython returns a value from "
                f"`{body}`, the analyzer admits no normal completion")
        elif expected != "normal":
            # Invariant 2. A subclass of the raised class counts: reporting
            # `LookupError` where CPython raises `IndexError` is sound.
            reported = reported or set()
            if expected not in reported and not (
                    reported & set(_superclasses(expected))):
                failures.append(
                    f"{tag}/{operation}: CPython raises {expected} from "
                    f"`{body}`, the analyzer reports "
                    f"{sorted(reported) or 'nothing'}")
        elif verbose:
            print(f"  {tag:8} {operation:14} CPython={expected:16} "
                  f"analyzer_normal={admits}")

    print(f"\nprobed {checked} (tag, operation) pairs against CPython "
          f"{sys.version.split()[0]}")
    print(f"{normal_checked} normal-completion checks, "
          f"{raise_checked} raise-reporting checks")
    print(f"{len(skips)} skipped, {len(failures)} unsound")
    # Always, not only under `--verbose`: a skip is coverage that did not happen,
    # and in a healthy run there are none, so this is silent when it should be.
    for skip in skips:
        print(f"  skip {skip}")
    for failure in failures:
        print(f"FAIL {failure}")
    # A probe that checked nothing has not passed. Every pair skipping at once
    # means the analyzer could not be run at all, and reporting that as success
    # is the failure mode this gate exists to catch in the interpreter.
    if normal_checked + raise_checked == 0:
        print("FAIL no (tag, operation) pair was checked at all -- the analyzer "
              "produced no sites, so this run proves nothing")
        return 1
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
