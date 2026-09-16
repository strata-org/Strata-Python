"""Run every selected method through pyInterpret, with bounded parallelism.

Per method: compile to Ion, then execute with pyInterpret. Both are independent across
methods, so they run in a worker pool.

The verifier is deliberately NOT run here. Its verdicts are conditional -- every one
reads "always true/false if reached, reachability unknown" -- so pairing them with an
oracle needs a reachability fact and a per-obligation location join, which is a
different and much heavier piece of machinery. The interpreter answers the question
this suite asks directly: run the same program CPython ran, and see whether Strata
agrees.

The pool is deliberately SMALL and fixed rather than sized to the machine. This suite
is one of ~21 test files that `StrataPythonTestExtra`'s testMain launches
concurrently, and a build in development was killed for low memory at that
concurrency before this suite did any work at all. An unbounded pool here would
multiply that. CPython's own regrtest makes the same call with `-j`.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import dataclasses
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import time

DEFAULT_WORKERS = 4


@dataclasses.dataclass
class Stage:
    ok: bool
    detail: str = ""


# The exit code this module uses for a timeout, matching the shell convention.
_TIMEOUT_RC = 124


def _run(cmd: list[str], cwd: str | None, env: dict, timeout: int) -> tuple[int, str]:
    try:
        p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True,
                           text=True, timeout=timeout)
        return p.returncode, (p.stdout or "") + (p.stderr or "")
    except subprocess.TimeoutExpired:
        return _TIMEOUT_RC, "TIMEOUT"


def classify_interpret(rc: int, out: str) -> tuple[str, str]:
    """Bucket a pyInterpret run BY EXIT CODE, per the package review policy that
    "translator diagnostic strings on stderr are not a stable interface. Consumers
    classify runs by exit code and the `RESULT:`/`DETAIL:` lines only, never by
    message wording" (AGENTS.md).

    pyInterpret emits no `RESULT:`/`DETAIL:` line, so the exit code is all there is:

        0  ran to completion
        1  Strata could not translate the program
        2  a runtime problem

    Exit 2 conflates the two cases this suite most wants to separate -- an assertion
    the interpreter evaluated to FALSE (a disagreement with CPython, possibly a bug)
    and an expression it could not reduce (a coverage gap). Telling them apart would
    mean matching on wording, so it is left to triage, and the raw first line is
    carried in `detail` for that. Making the split reliable needs pyInterpret to emit
    a RESULT line the way pyAnalyze* does.
    """
    first = next((l.strip() for l in out.splitlines()
                  if l.strip() and not l.startswith("[start]")), "")
    if rc == 0:
        return "ran", ""
    if rc == _TIMEOUT_RC:
        return "timeout", ""
    if rc == 1:
        return "untranslatable", first[:300]
    if rc == 2:
        return "runtimeProblem", first[:300]
    return "error", first[:300]


def process(method: dict, paths: dict, env: dict, timeout: int) -> dict:
    stem = method["stem"]
    gen = pathlib.Path(paths["gen"])
    src = gen / f"{stem}.py"
    ion = gen / f"{stem}.python.st.ion"

    rc, out = _run(
        [paths["python"], "-m", "strata_python.gen", "-q", "py_to_strata",
         "--dialect", "dialects/Python.dialect.st.ion", str(src), str(ion)],
        cwd=paths["strata_python"], env=env, timeout=timeout)
    if rc == _TIMEOUT_RC:
        # A py_to_strata HANG is not a coverage gap. Folding it into `parse: False`
        # made compare.py record it as `untranslatable`, which is the expected state for
        # most methods and is baselined -- so a translation-stage performance regression
        # would have been invisible. The interpreter stage already separates the two via
        # classify_interpret; this does the same.
        return {"stem": stem, "parse": False, "parseTimeout": True,
                "parseDetail": "py_to_strata timed out"}
    if rc != 0 or not ion.exists():
        return {"stem": stem, "parse": False,
                "parseDetail": out.strip().splitlines()[-1][:300] if out.strip() else ""}

    irc, iout = _run([paths["interpreter"], str(ion), "--v2"], None, env, timeout)
    (gen / f"{stem}.interp").write_text(iout)
    ibucket, idetail = classify_interpret(irc, iout)

    # Run the GENERATED program under CPython too. This is the invariant the whole
    # comparison rests on: if the lowering preserved meaning, the generated program
    # must behave as the original method did. It is not a formality -- it caught
    # test_generators.test_name, which asserts on `__qualname__` and so cannot survive
    # being lifted into a function of ours.
    #
    # Each program gets its OWN working directory. Some CPython tests create files or
    # directories relative to the cwd -- test_fstring makes a `tempcwd` -- so with a
    # shared cwd two of them racing under the worker pool made one fail with
    # FileExistsError, and the two swapped buckets between runs. A baseline that
    # flickers is worse than no baseline.
    genv = dict(env, PYTHONPATH=paths["corpus_lib"], PYTHONWARNINGS="ignore")
    with tempfile.TemporaryDirectory(prefix="cpython-oracle-cwd.") as cwd:
        grc, gout = _run([paths["python"], str(src)], cwd, genv, timeout)
    gdetail = "" if grc == 0 else (gout.strip().splitlines() or [""])[-1][:300]

    # A HANG in the reference run is a harness or performance problem, not evidence that
    # the lowering changed the program's meaning -- the same distinction the translation
    # stage needs above. It matters more here: `loweringBroken` is an excluded bucket
    # whose transitions the baseline diff ignores, so collapsing a timeout into it would
    # swallow the signal completely.
    generated = ("clean" if grc == 0 else
                 "timeout" if grc == _TIMEOUT_RC else "failed")
    if generated == "timeout":
        gdetail = "generated program timed out under CPython"

    return {"stem": stem, "parse": True,
            "interpret": ibucket, "interpretDetail": idetail,
            "generatedUnderCPython": generated,
            "generatedDetail": gdetail}


def main(argv: list[str]) -> int:
    here = pathlib.Path(__file__).parent
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", default=str(here / "build"))
    ap.add_argument("--workers", type=int,
                    default=int(os.environ.get("CPYTHON_ORACLE_WORKERS",
                                               DEFAULT_WORKERS)))
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--corpus-lib", default="",
                    help="dir holding the extracted `test` package, for the "
                         "generated-program check (imports test.support)")
    args = ap.parse_args(argv[1:])

    pkg = here.parent.parent
    build = pathlib.Path(args.build)
    selection = json.loads((build / "selection.json").read_text())
    methods = selection["methods"]

    paths = {
        "gen": str(build / "gen"),
        "python": os.environ.get("PYTHON", "python3"),
        "strata_python": str(pkg / "Python/strata-python"),
        "interpreter": str(pkg / ".lake/build/bin/pyInterpret"),
        "corpus_lib": args.corpus_lib,
    }
    env = dict(os.environ)

    t0 = time.time()
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futs = [pool.submit(process, m, paths, env, args.timeout) for m in methods]
        for i, f in enumerate(concurrent.futures.as_completed(futs), 1):
            results.append(f.result())
            if i % 50 == 0:
                print(f"    {i}/{len(methods)} ({time.time()-t0:.0f}s)", flush=True)
    elapsed = time.time() - t0

    (build / "engines.json").write_text(json.dumps(
        {"workers": args.workers,
         "elapsedSeconds": round(elapsed, 1), "results": results},
        indent=2, sort_keys=True) + "\n")

    parse_fail = sum(1 for r in results if not r["parse"])
    counts: dict[str, int] = {}
    for r in results:
        if r["parse"]:
            counts[r["interpret"]] = counts.get(r["interpret"], 0) + 1
    print(f"  {len(results)} methods in {elapsed:.0f}s "
          f"({args.workers} workers, {elapsed/max(len(results),1):.2f}s/method)")
    if parse_fail:
        print(f"  py_to_strata failures: {parse_fail}")
    print("  pyInterpret: " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())))
    broke = [r for r in results if r.get("generatedUnderCPython") == "failed"]
    if broke:
        print(f"  LOWERING BROKEN for {len(broke)} method(s): the generated program "
              f"does not behave as the original under CPython")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
