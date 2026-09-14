"""The three-stage pipeline: CPython AST dump -> Lean checker+analyzer ->
HTML render. Each stage is replayable from the previous stage's file.

Usage: python3 pipeline.py FILE.py [FILE.py...] [-o out.html]
       python3 pipeline.py FILE.py --logs-only     # stop after the logs

The Lean executable is .lake/build/bin/pylate (build with `lake build` in
the package root). Intermediate files land next to the
output: FILE.ast.json and FILE.log.json.
"""
import json
import os
import subprocess
import sys

import paths

HERE = paths.HARNESS
LEAN_BIN = paths.PYLATE


def run_one(path, workdir, policy=None, sorts=None):
    base = os.path.splitext(os.path.basename(path))[0]
    log_path = os.path.join(workdir, base + ".log.json")
    # stage 1: the analyzer's input -- the Strata AST, read through StrataDDM.
    try:
        ast_path = paths.make_analyzer_input(path, os.path.join(workdir, base))
    except subprocess.CalledProcessError as error:
        detail = (error.stderr or b"").decode(errors="replace").strip()
        raise SystemExit(f"{path}: building the analyzer input failed: {detail}")
    # stage 2: subset check + analysis
    pol = ["--policy", policy] if policy else []
    if sorts:
        pol += ["--sorts", sorts]
    lean = subprocess.run(
        [LEAN_BIN, ast_path, "--src", path, "-o", log_path, *pol],
        capture_output=True, text=True)
    if lean.returncode != 0:
        raise SystemExit(f"{path}: pylate failed: {lean.stderr}")
    with open(log_path) as f:
        log = json.load(f)
    n = (len(log["violations"]) if log["status"] == "rejected"
         else log["summary"]["sites"])
    print(f"{path}: {log['status']} "
          f"({'violations' if log['status'] == 'rejected' else 'sites'}: {n})")
    return log_path


def main():
    args = sys.argv[1:]
    outpath, logs_only, policy, sorts, files = \
        "pipeline_render.html", False, None, None, []
    i = 0
    while i < len(args):
        if args[i] == "-o":
            outpath = args[i + 1]
            i += 2
        elif args[i] == "--policy":
            policy = args[i + 1]
            i += 2
        elif args[i] == "--sorts":
            sorts = args[i + 1]
            i += 2
        elif args[i] == "--logs-only":
            logs_only = True
            i += 1
        else:
            files.append(args[i])
            i += 1
    workdir = os.path.dirname(os.path.abspath(outpath)) or "."
    logs = [run_one(p, workdir, policy, sorts) for p in files]
    if logs_only:
        return
    # stage 3: render
    subprocess.run(
        [sys.executable, os.path.join(HERE, "render_log.py"),
         *logs, "-o", outpath], check=True)


if __name__ == "__main__":
    main()
