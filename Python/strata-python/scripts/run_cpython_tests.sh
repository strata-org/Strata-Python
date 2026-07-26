#!/bin/bash
set -euo pipefail

# Clone the CPython sources for a given version and run the Strata Python
# generator over every file in its test suite, checking that each round-trips
# through Strata's Ion (de)serializer.
#
# This script handles orchestration only: cloning CPython, selecting the
# interpreter, and computing the list of files expected to fail. The actual
# per-file work (running `strata_python.gen py_to_strata` and verifying the Ion
# round-trip) is done by the Lean test `StrataPythonTestExtra/CpythonDiffTest`,
# which we drive here by setting environment variables and running `lake test`.
# Doing the round-trip in Lean means we no longer need a separate `strata` CLI
# build.
#
# If the FAIL_FAST variable is set to a non-empty string, the Lean test stops
# on the first unexpected outcome. This is predominantly used in CI.

if [ "$#" -ne 1 ]; then
    >&2 echo "Missing CPython version to test"
    exit 1
fi

VER="$1"
prefix="cpython-$VER"
if [ -d "$prefix" ]; then
  echo "Skipping download: $prefix already exists"
else
  git clone https://github.com/python/cpython.git --branch "$VER" --depth 1 "$prefix"
fi

# Files in the CPython test suite that are expected to fail to parse (and so
# should fail the round-trip). Listed as path suffixes, one per line; the Lean
# test matches a discovered file when its path ends with one of these.
expected_failures=""
case "$VER" in
  3.14|3.13|3.11)
    expected_failures="/tokenizedata/bad_coding.py
/tokenizedata/bad_coding2.py
/tokenizedata/badsyntax_3131.py
/tokenizedata/badsyntax_pep3120.py"
    ;;
  3.12)
    expected_failures="/tokenizedata/bad_coding.py
/tokenizedata/bad_coding2.py
/tokenizedata/badsyntax_3131.py
/tokenizedata/badsyntax_pep3120.py
/test_lib2to3/data/different_encoding.py
/test_lib2to3/data/false_encoding.py
/test_lib2to3/data/bom.py
/test_lib2to3/data/py2_test_grammar.py
/test_lib2to3/data/crlf.py"
    ;;
esac

# Select the interpreter. Prefer the requested version via mise, falling back to
# python3; export it as PYTHON so the Lean test's `withPython` picks it up.
if command -v mise >/dev/null 2>&1 && mise where "python@$VER" >/dev/null 2>&1; then
  PYTHON="$(mise where "python@$VER")/bin/python"
else
  PYTHON="python3"
fi
export PYTHON

# Directories used by the Lean test.
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
STRATA_PYTHON_PKG="$(cd "$SCRIPT_DIR/../../.." && pwd)"  # repo root (lake package)
TOOLS_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# Write the expected-failures list to a plaintext file the Lean test reads.
expected_file="$(mktemp)"
trap 'rm -f "$expected_file"' EXIT
printf '%s\n' "$expected_failures" > "$expected_file"

export CPYTHON_DIR="$TOOLS_DIR/$prefix/Lib/test"
export CPYTHON_EXPECTED_FAILURES="$expected_file"
if [ -n "${FAIL_FAST-}" ]; then
  export CPYTHON_FAIL_FAST=1
fi

echo "Running CPython differential test over $CPYTHON_DIR with PYTHON=$PYTHON"
(cd "$STRATA_PYTHON_PKG" && lake test -- CpythonDiffTest)
