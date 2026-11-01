"""The CPython side of the oracle's second backend, which runs the programs with the Python
semantics (`pydyn run`).

    runner_dyn.py --build BUILD [--filter F] [--workers N]

It selects and generates the methods as the existing suite does (`plan.py`, into `BUILD`), runs
each method on its pristine source under CPython (`oracle.py`), and runs each generated program
under CPython twice, with `PYTHONHASHSEED` 0 and 1, through the trace script of the Python
semantics (`StrataPythonTest/Dyn/trace.py`). It writes `BUILD/dyn.json`: for each method, its
generated program, and either the bucket that excludes it or CPython's two traces. A method is
excluded as `oracleNotClean` when it doesn't run cleanly under CPython, and as `loweringBroken`
when it does but its generated program fails as a plain program, or a traced run of it doesn't
end with the outcome `ok`. The Lean driver, `StrataPythonTestExtra/CpythonOracleDynTest.lean`,
joins the two traces with `SemDiff.joinRuns`, as `SemDiff.cpythonTrace` does, runs the semantics
on each program and keeps the verdicts. It exits 3 when CPython 3.12 or its sources are not
available, as the existing suite does.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import pathlib
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
TRACE = HERE.parent / "Dyn" / "trace.py"


def run(cmd, cwd=None, env=None, timeout=600):
    try:
        p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True,
                           timeout=timeout)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return 124, "", "TIMEOUT"


def outcome_of(trace):
    """The first line of a trace's outcome section: `ok`, or `raised …`. The trace starts with
    `--- stdout <n>` and the output's `n` characters (trace.py)."""
    head, _, rest = trace.partition("\n")
    if not head.startswith("--- stdout "):
        return head  # `--- syntax error`: CPython doesn't compile the program
    n = int(head.removeprefix("--- stdout "))
    after = rest[n:].removeprefix("\n")
    assert after.startswith("--- outcome\n"), "unexpected trace format"
    return after.removeprefix("--- outcome\n").split("\n", 1)[0]


def cpython_side(method, gen, py, corpus_lib, timeout):
    """The generated program's plain run and its two traced runs under CPython, each in a fresh
    interpreter. The plain run has its own working directory, and `trace.py` runs the program in a
    fresh empty directory of its own. A plain
    run that fails, or a traced run that doesn't end with the outcome `ok`, means that the
    generated program doesn't behave as the method did (`loweringBroken`)."""
    stem = method["stem"]
    src = gen / f"{stem}.py"
    env = dict(os.environ, PYTHONPATH=corpus_lib, PYTHONWARNINGS="ignore")
    with tempfile.TemporaryDirectory(prefix="oracle-dyn-cwd.") as cwd:
        rc, out, err = run([py, str(src)], cwd, env, timeout)
    if rc == 124:
        return {"stem": stem, "error": "the generated program timed out under CPython"}
    if rc != 0:
        return {"stem": stem, "excluded": "loweringBroken",
                "detail": ((err or out).strip().splitlines() or [""])[-1][:300]}
    traces = []
    for seed in ("0", "1"):
        with tempfile.TemporaryDirectory(prefix="oracle-dyn-cwd.") as cwd:
            rc, out, err = run([py, str(TRACE), str(src)], cwd,
                               dict(env, PYTHONHASHSEED=seed), timeout)
        if rc == 124:
            return {"stem": stem, "error": "the generated program timed out under CPython"}
        if rc != 0:
            return {"stem": stem, "error": f"trace.py failed: {err.strip()[-300:]}"}
        outcome = outcome_of(out)
        if outcome != "ok":
            return {"stem": stem, "excluded": "loweringBroken", "detail": outcome[:300]}
        traces.append(out)
    return {"stem": stem, "program": str(src), "traces": traces}


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("--build", required=True)
    ap.add_argument("--filter", default="")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=600)
    args = ap.parse_args(argv[1:])
    py = os.environ.get("PYTHON", sys.executable)
    build = pathlib.Path(args.build).resolve()

    rc, out, _ = run([py, "-c", "import sys; print(sys.version_info[:2] == (3, 12))"])
    if rc != 0 or out.strip() != "True":
        print(f"SKIP: {py} is not CPython 3.12", file=sys.stderr)
        return 3
    sys.path.insert(0, str(HERE))
    from corpus import find_tarball
    try:
        find_tarball()
    except Exception:
        print("SKIP: CPython corpus unavailable", file=sys.stderr)
        return 3

    plan = [py, str(HERE / "plan.py"), str(HERE / "manifest.txt"), str(build)]
    if args.filter:
        plan += ["--filter", args.filter]
    rc, out, err = run(plan)
    if rc != 0:
        print(out + err, file=sys.stderr)
        return 1
    selection = json.loads((build / "selection.json").read_text())
    rc, out, err = run([py, str(HERE / "oracle.py"), str(build / "selection.json"),
                        str(build / "oracle.json")])
    if rc != 0:
        print(out + err, file=sys.stderr)
        return 1
    clean = {}
    for f in json.loads((build / "oracle.json").read_text())["files"]:
        clean.update(f["outcomes"])

    gen = build / "gen"
    results = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futs = []
        for m in selection["methods"]:
            oc = clean.get(m["stem"])
            if oc is None:
                results.append({"stem": m["stem"], "error": "no oracle outcome recorded"})
            elif oc != "clean":
                results.append({"stem": m["stem"], "excluded": "oracleNotClean", "detail": oc})
            else:
                futs.append(pool.submit(cpython_side, m, gen, py, selection["corpusLib"],
                                        args.timeout))
        results += [f.result() for f in futs]
    results.sort(key=lambda r: r["stem"])
    (build / "dyn.json").write_text(json.dumps({"results": results}, indent=1) + "\n")
    print(f"runner_dyn: {len(results)} methods, "
          f"{sum('traces' in r for r in results)} with a CPython trace, "
          f"{sum('excluded' in r for r in results)} excluded, "
          f"{sum('error' in r for r in results)} errors")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
