#!/bin/bash
# Run part of CPython's regression suite as an oracle for the Python front end.
#
# For each eligible test method (see selector.py):
#   1. generate a single-method program, with each unittest assertion lowered to
#      the plain `assert` it means
#   2. execute it with pyInterpret
#   3. run the PRISTINE method under CPython to learn whether it completes cleanly
#   4. compare the interpreter's outcome against CPython's and bucket it
#
# Findings do not fail the run: a construct Strata cannot handle is what this suite
# exists to surface. What fails is a DIFFERENCE from baseline.txt, which records the
# outcome per method and is checked in -- so a regression is visible and an improvement
# has to be recorded. Regenerate with --update.
#
# Flags:
#   --manifest <file>   file list to draw from (default manifest.txt)
#   --filter <substr>   only methods whose stem contains <substr>
#   --keep              keep the build directory
#   --workers <n>       bounded parallelism (default 4, or $CPYTHON_ORACLE_WORKERS)
#   --update            rewrite baseline.txt from this run instead of diffing it
set -uo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
PKG="$(cd "$HERE/../.." && pwd)"
BUILD="$HERE/build"

MANIFEST="$HERE/manifest.txt"
FILTER=""
KEEP=0
UPDATE=""
WORKERS="${CPYTHON_ORACLE_WORKERS:-4}"
while [ $# -gt 0 ]; do
  case "$1" in
    --manifest) MANIFEST="$2"; shift 2 ;;
    --filter)   FILTER="$2"; shift 2 ;;
    --keep)     KEEP=1; shift ;;
    --workers)  WORKERS="$2"; shift 2 ;;
    --update)   UPDATE="--update"; shift ;;
    *) echo "unknown flag: $1" >&2; exit 2 ;;
  esac
done

# pyInterpret is in the package's defaultTargets, so brazil-build has already
# produced it by the time tests run and this `lake build` is a no-op.
#
# That listing matters. Without it, this script and run_py_interpret.sh both compiled
# pyInterpret from scratch AT THE SAME TIME -- testMain launches the test files
# concurrently -- and the two lake invocations clobbered each other's intermediate
# objects. The visible failure was in a THIRD suite: AnalyzeGoldenTest died compiling
# StrataLaurel.Implementation.EliminateDeterministicHoles with "no such file or
# directory". It is a race, so it passed three builds before it bit.
( cd "$PKG" && lake build pyInterpret ) || exit 1
if [ ! -x "$PKG/.lake/build/bin/pyInterpret" ]; then
  echo "ERROR: missing $PKG/.lake/build/bin/pyInterpret after lake build" >&2
  exit 2
fi

# The build exports PYTHON; fall back to python3.
PY="${PYTHON:-python3}"

# Exit 3 tells the Lean driver to treat this as a SKIP rather than a failure: the
# environment cannot support the suite, which is not a statement about the code.
#
# Both checks matter, and both were found by running under a bare `lake test`:
#
#   * The interpreter must be able to parse the CPython sources. `plan.py` uses
#     `ast` on Lib/test/*.py, so an older Python silently drops every file using
#     syntax it does not know -- system python3.9 selected 270 methods where 3.12
#     selects 337, with no error at all. Under-reporting is worse than skipping.
#   * `strata_python.gen` must be importable, or every method fails to compile and
#     the run reports a wall of failures that say nothing about Strata.
#
# brazil-build exports a PYTHON that satisfies both; a hand-run shell may not.
if ! "$PY" -c "
import sys
assert sys.version_info[:2] >= (3, 12), f'need >=3.12 to parse the corpus, have {sys.version.split()[0]}'
import strata_python.gen
" 2>/dev/null; then
  echo "SKIP: \$PY ($PY) is not usable for this suite." >&2
  "$PY" -c "
import sys
print(f'  interpreter: {sys.version.split()[0]} (need >= 3.12 to parse CPython 3.12 sources)', file=sys.stderr)
try:
    import strata_python.gen
except Exception as e:
    print(f'  strata_python.gen: {type(e).__name__}: {e}', file=sys.stderr)
" 2>&1 >&2 || true
  echo "  set PYTHON and PYTHONPATH as the build does, or run via brazil-build." >&2
  exit 3
fi

if ! "$PY" -c "
import sys, pathlib
sys.path.insert(0, '$HERE')
from corpus import find_tarball
find_tarball()
" 2>/dev/null; then
  echo "SKIP: CPython corpus unavailable (brazil-path could not resolve CPython312Runtime)" >&2
  exit 3
fi

echo "=== plan ==="
# --filter is applied at SELECTION time, so every later stage sees exactly the
# methods that were generated. Filtering later would leave the rest in
# selection.json with no engine output and report them all as failures.
PLAN_ARGS=("$MANIFEST" "$BUILD")
if [ -n "$FILTER" ]; then PLAN_ARGS+=(--filter "$FILTER"); fi
"$PY" "$HERE/plan.py" "${PLAN_ARGS[@]}" || exit 1


echo
echo "=== pyInterpret ($WORKERS workers) ==="
CORPUS_LIB="$("$PY" -c "
import json, sys
print(json.load(open('$BUILD/selection.json'))['corpusLib'])
")"
"$PY" "$HERE/runner.py" --build "$BUILD" --workers "$WORKERS" \
      --corpus-lib "$CORPUS_LIB" || exit 1

echo
echo "=== oracle (CPython $("$PY" -V 2>&1 | cut -d' ' -f2)) ==="
"$PY" "$HERE/oracle.py" "$BUILD/selection.json" "$BUILD/oracle.json" || exit 1

echo
echo "=== compare ==="
"$PY" "$HERE/compare.py" "$BUILD/selection.json" "$BUILD/oracle.json" \
      "$BUILD" "$BUILD/report.json" $UPDATE
rc=$?

if [ "$KEEP" -eq 0 ]; then
  rm -rf "$BUILD/gen"
fi
exit $rc
