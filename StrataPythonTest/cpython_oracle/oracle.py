"""Run the selected CPython test methods under CPython and record the outcome.

The method runs UNMODIFIED, through real `unittest`, on the pristine source from the
tarball, so what executes is exactly what CPython's own suite executes.

The outcome needed is one bit per method: did it complete without raising? That is
the whole expectation this suite checks Strata against, because these are CPython's
own passing tests -- a method that raises under CPython means the corpus or the
environment is wrong, not Strata.

An earlier version wrapped every `assert*` method to capture a verdict per assertion,
keyed by `co_positions()`, so per-obligation verdicts could be joined against the
verifier's SARIF. With the verifier out of this suite there is nothing to join, and
the per-method outcome is all the interpreter comparison needs.
"""
from __future__ import annotations

import json
import os
import pathlib
import sys
import types
import unittest
import warnings


def run_file(relpath: str, source: str, methods: list[dict],
             real_path: str | None = None) -> dict:
    """Execute `methods` from `source`; return each method's outcome.

    The module is compiled under its REAL extracted path, not a synthetic name. Several
    CPython tests assert on traceback locations (test_exceptions, the
    `test_exception_locations` family), and under a made-up filename they fail --
    which showed up as six spurious `oracleNotClean` exclusions that said nothing about
    Strata.
    """
    filename = real_path or f"<cpython-oracle:{relpath}>"
    mod = types.ModuleType(f"_oracle_{relpath.replace('.', '_').replace('/', '_')}")
    mod.__file__ = filename
    # Compiling the corpus raises CPython's own SyntaxWarnings (test_fstring's
    # deliberate bad escapes, for one). They say nothing about Strata and would be the
    # loudest thing in the output.
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        code = compile(source, filename, "exec")
        sys.modules[mod.__name__] = mod
        exec(code, mod.__dict__)

    outcomes: dict[str, str] = {}
    detail: dict[str, str] = {}

    # `TestCase.run` drives setUp and tearDown but NOT setUpClass or setUpModule -- the
    # suite and loader do those. The generated program calls setUpClass itself, so
    # without this the oracle and the program it is the expectation for would run under
    # different fixtures, and a class-level fixture would make them disagree for a
    # reason that has nothing to do with Strata.
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        if hasattr(mod, "setUpModule"):
            try:
                mod.setUpModule()
            except Exception:
                pass
    classes_setup: set[str] = set()

    for m in methods:
        klass = getattr(mod, m["cls"])
        if m["cls"] not in classes_setup:
            classes_setup.add(m["cls"])
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                try:
                    klass.setUpClass()
                except Exception:
                    pass
        case = klass(m["method"])
        result = unittest.TestResult()
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            case.run(result)
        if result.errors:
            outcomes[m["stem"]] = "error"
            detail[m["stem"]] = result.errors[0][1].strip().splitlines()[-1][:200]
        elif result.failures:
            outcomes[m["stem"]] = "failed"
            detail[m["stem"]] = result.failures[0][1].strip().splitlines()[-1][:200]
        elif result.skipped:
            # A skip-only decorator is dropped from the GENERATED program but is still
            # live here, because the oracle runs the pristine source through real
            # unittest. A skipped method leaves errors and failures empty, so without
            # this it was recorded as `clean` and the interpreter was then compared
            # against a test that never ran. compare.py buckets any non-clean outcome
            # as an exclusion, which is the right answer: there is no expectation.
            outcomes[m["stem"]] = "skipped"
            detail[m["stem"]] = (result.skipped[0][1] or "skipped")[:200]
        else:
            outcomes[m["stem"]] = "clean"
    return {"file": relpath, "outcomes": outcomes, "detail": detail}


def main(argv: list[str]) -> int:
    """oracle.py <selection.json> <out.json>"""
    selection = json.loads(pathlib.Path(argv[1]).read_text())

    sys.path.insert(0, str(pathlib.Path(__file__).parent))
    from corpus import Corpus

    # The pristine files import `test.support`; plan.py already extracted it from the
    # same tarball, so the helpers match the file under test exactly.
    sys.path.insert(0, selection["corpusLib"])

    results = []
    with Corpus() as corpus:
        by_file: dict[str, list[dict]] = {}
        for m in selection["methods"]:
            by_file.setdefault(m["file"], []).append(m)
        test_dir = pathlib.Path(selection["corpusLib"]) / "test"
        # Run from the corpus test directory: some tests open data files by relative
        # path (test_float's formatfloat_testcases.txt), and from anywhere else they
        # fail for a reason that has nothing to do with Strata.
        prev = os.getcwd()
        os.chdir(test_dir)
        try:
            for relpath, methods in sorted(by_file.items()):
                results.append(run_file(relpath, corpus.read(relpath), methods,
                                        str(test_dir / relpath)))
        finally:
            os.chdir(prev)

    pathlib.Path(argv[2]).write_text(json.dumps(
        {"cpython": selection.get("cpython", ""), "files": results},
        indent=2, sort_keys=True) + "\n")

    counts: dict[str, int] = {}
    for r in results:
        for v in r["outcomes"].values():
            counts[v] = counts.get(v, 0) + 1
    total = sum(counts.values())
    print(f"oracle: {total} methods across {len(results)} file(s) -- "
          + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
