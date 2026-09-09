#!/bin/bash

# Usage: ./run_py_interpret.sh [--v2] [--filter <pattern>] [--fuel <n>] [--keep-all-files <dir>] [--verbose] [--update]
#
# Runs pyInterpret on all test_*.py files and reports pass/fail.
#
# With --v2, run the V2 front end (Resolution → Translation → Elaboration → Core)
# instead of V1 (Python → Laurel → Core).  Each front end has its own set of
# expectations: expected_interpret/ holds the V2 ones and expected_interpret_v1/ the
# V1 ones.  See expected_interpret/README.md for why the sets sit at those paths.
#
# Expected outcomes are controlled by files in that front end's directory:
#   - No .expected/.skip → run test, assert exit code 0 (PASS)
#   - .expected file     → run test, assert non-zero exit and output matches
#                          the regex pattern in the file
#   - .skip file         → skip test (file contents used as reason)
#
# The V1 run covers only the hand-written cases.  The imported regression corpus is
# V2-only, marked by a `.desired` sidecar in expected_interpret/ -- that file records
# what a case ought to conclude (read by completeness_report.py) and doubles as the
# marker for "imported", since every imported case has one and no other case does.
#
# Options:
#   --v2                Run the V2 front end instead of V1
#   --filter <pattern>  Only run tests whose name contains <pattern>
#   --fuel <n>          Set the interpreter fuel limit (default: 100000)
#   --verbose           Show full interpreter output on failure
#   --update            Regenerate .expected files from actual output

set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TESTS_DIR="$SCRIPT_DIR/tests"
STRATA_PYTHON_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# `run_py_analyze.sh` runs the same corpus and regenerates the same
# tests/*.python.st.ion scratch files, and the test driver (Strata.IOTests.testMain)
# launches every test file concurrently, so both suites can be in flight at once.
# Serialize them on a shared lock rather than giving each its own scratch directory:
# the Ion path appears in analyzer and interpreter output, and expectations match on
# it. The lock is released when the script exits.
LOCK_FILE="$SCRIPT_DIR/.corpus-ion.lock"
if command -v flock > /dev/null 2>&1; then
    exec 9> "$LOCK_FILE"
    if ! flock -n 9; then
        echo "Waiting for the shared tests/*.python.st.ion lock (the other corpus suite is running) ..."
        flock 9
    fi
fi

# Per-invocation timeout for one interpreter run. `--fuel` bounds execution steps but
# not translation, and the corpus is large enough that a single non-terminating case
# would hang CI. A timeout is reported as a normal failure so --update can record it.
INTERPRET_TIMEOUT="${INTERPRET_TIMEOUT:-60}"

passed=0
errors=0
skipped=0
filter=""
keepAllFiles=""
fuel=""
verbose=0
update=0
v2=0

while [ $# -gt 0 ]; do
    case "$1" in
        --filter) filter="$2"; shift ;;
        --keep-all-files) keepAllFiles="--keep-all-files $2"; shift ;;
        --fuel) fuel="--fuel $2"; shift ;;
        --verbose) verbose=1 ;;
        --update) update=1 ;;
        --v2) v2=1 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
    shift
done

# Which front end to run, and where its expectations live. Presence of
# <expected_dir>/<name>.expected is what says "this case fails under that front end";
# absence says "it passes". The V2 run also reports how far apart the two sets are.
if [ $v2 -eq 1 ]; then
    front_end="V2"
    v2_flag="--v2"
    EXPECTED_DIR="$SCRIPT_DIR/expected_interpret"
    OTHER_DIR="$SCRIPT_DIR/expected_interpret_v1"
else
    front_end="V1"
    v2_flag=""
    EXPECTED_DIR="$SCRIPT_DIR/expected_interpret_v1"
    OTHER_DIR=""
fi

# Python interpreter. Prefer the one the build exported (PYTHON), which has
# strata_python importable; fall back to python3 for manual local runs.
python="${PYTHON:-python3}"

# Build the interpreter once and invoke the binary per test. `lake exe` would
# re-check the build on every one of the ~1,500 cases, which dominates the run.
(cd "$STRATA_PYTHON_DIR" && lake build pyInterpret > /dev/null 2>&1)
interpreter="$STRATA_PYTHON_DIR/.lake/build/bin/pyInterpret"
if [ ! -x "$interpreter" ]; then
    echo "ERROR: pyInterpret was not built at $interpreter"
    exit 1
fi

echo "Running the ${front_end} front end (pyInterpret ${v2_flag:-(default)})"

# The one line of a failure that names it. Every shape the interpreter produces puts
# that line FIRST and any elaboration after it:
#
#   Exception: Unsupported construct: class decorators are not supported
#   AST: { ann := { start := { byteIdx := 0 }, ...        <- pretty-printed dump
#
#   Run strata --help for additional help.                <- exitFailure's hint
#
# so this drops the continuation (indented lines and the `AST:` header), the hint,
# blank lines and Lean runtime backtraces, then takes the head. Taking the tail
# instead yields a leaf of the AST dump, which names nothing and moves with
# unrelated pretty-printer changes. The leading "Exception: " that the CLI
# framework's `exitFailure` adds is stripped so a generated pattern reads like the
# rest of the corpus.
failure_reason() {
    grep -v "^$" | grep -v "backtrace:" | grep -v "^trace:" \
      | grep -v "for additional help\.$" \
      | grep -v "^[[:space:]]" | grep -v "^AST:" \
      | head -1 | sed 's/^Exception: //'
}

# Turn one failure line into the pattern stored in a .expected file. Everything is
# matched literally except the identifiers that are not stable across runs.
# Three kinds, all of which move for reasons unrelated to the case under test:
#
#   assert(553)                              assertion/assumption numbering
#   byteIdx := 2532                          Ion byte offset
#   file.python.st.ion(2532-2575)            Ion source span
#   StrataPython.Resolution:1739:7           Lean source line:col in a PANIC
#   $__ty2468                                generated type variable
#
# Each of these moves for reasons unrelated to the case: a mainline edit to
# Resolution.lean turned `:1470:7` into `:1739:7`, and a prelude change turned
# `$__ty2468` into `$__ty2543`. Every one was found by a CI failure rather than up
# front, so treat a new generated identifier as belonging here by default.
derive_pattern() {
    # \x01 stands in for a single number and \x02 for an Ion source span while the
    # escaping pass runs; both are restored to regexes afterwards.
    sed -E 's/(assert|assume)\(([0-9]+)\)/\1(\x01)/g;
            s/byteIdx := [0-9]+/byteIdx := \x01/g;
            s/([A-Za-z0-9_.]):[0-9]+:[0-9]+/\1:\x01:\x01/g;
            s/(\$__[A-Za-z]+)[0-9]+/\1\x01/g;
            s/\(([0-9]+)-([0-9]+)\)/(\x02)/g' \
      | sed 's/[][(){}.*+?^$\\|]/\\&/g' \
      | sed 's/\x01/[0-9]+/g; s/\x02/[0-9]+-[0-9]+/g'
}

# Does $output match the pattern in $1?
#
# Tries the output as produced, then again with every run of whitespace collapsed
# to one space and newlines removed. A stored pattern is a single line with single
# spaces, so a diagnostic that a host wrapped or indented differently is the same
# failure and should match. This is why the retry exists: a case has twice failed on
# the aarch64 build host with an `actual:` line indistinguishable from its pattern,
# which is what a difference in invisible whitespace looks like in a log. The retry
# is additive -- it can only turn a mismatch into a match, never the reverse.
matches_pattern() {
    if printf '%s\n' "$output" | grep -qE "$1"; then
        return 0
    fi
    printf '%s' "$output" | tr '\n' ' ' | tr -s '[:space:]' ' ' | grep -qE "$1"
}

# Everything known about a mismatch. The failure line alone was not enough to
# diagnose the aarch64 case above -- it rendered identically to the pattern -- so
# also report the line's length and its bytes with non-printables made visible.
report_mismatch() {
    local reason
    reason=$(printf '%s\n' "$output" | failure_reason)
    echo "      actual: $reason"
    echo "      actual: ${#reason} chars, $(printf '%s\n' "$output" | wc -l) line(s) of output"
    echo "      actual: escaped: $(printf '%s' "$reason" | cat -v)"
}

for test_file in "$TESTS_DIR"/test_*.py; do
    [ -f "$test_file" ] || continue
    base_name=$(basename "$test_file" .py)

    # Apply name filter if specified
    if [ -n "$filter" ] && [[ "$base_name" != *"$filter"* ]]; then
        continue
    fi

    # The imported regression corpus is V2-only: V1 is slated for deletion, so
    # there is no reason to spend a run per case on it. A `.desired` sidecar is
    # exactly what marks an imported case -- all 1,168 have one and none of the
    # hand-written cases does -- so a new import is V2-only automatically.
    if [ $v2 -eq 0 ] && [ -f "$SCRIPT_DIR/expected_interpret/${base_name}.desired" ]; then
        continue
    fi

    expected_file="$EXPECTED_DIR/${base_name}.expected"
    skip_file="$EXPECTED_DIR/${base_name}.skip"
    ion_file="$TESTS_DIR/${base_name}.python.st.ion"

    # Check for skip file
    if [ -f "$skip_file" ]; then
        reason=$(cat "$skip_file")
        echo "SKIP: $base_name — $reason"
        skipped=$((skipped + 1))
        continue
    fi

    # Compile Python to Ion
    if ! (cd "$STRATA_PYTHON_DIR/Python/strata-python" && "$python" -m strata_python.gen py_to_strata \
        --dialect "dialects/Python.dialect.st.ion" \
        "$test_file" "$ion_file") 2>/dev/null; then
        echo "SKIP (parse): $base_name"
        skipped=$((skipped + 1))
        continue
    fi

    # Run interpreter
    rel_ion="StrataPythonTest/tests/${base_name}.python.st.ion"
    output=$(cd "$STRATA_PYTHON_DIR" && timeout "$INTERPRET_TIMEOUT" "$interpreter" $v2_flag $fuel $keepAllFiles \
        "$rel_ion" 2>&1)
    exit_code=$?
    # `timeout` reports 124; give it a stable one-line output so --update can record it
    # instead of writing an empty pattern.
    if [ $exit_code -eq 124 ]; then
        output="pyInterpret timed out after ${INTERPRET_TIMEOUT}s"
    fi

    # Clean up Ion file
    rm -f "$ion_file"

    if [ -f "$expected_file" ]; then
        # Expected file exists → test should fail, output should match regex
        pattern=$(cat "$expected_file")

        if [ -z "$pattern" ]; then
            echo "ERR:  $base_name (empty .expected file — must contain a pattern)"
            errors=$((errors + 1))
            continue
        fi

        if [ $update -eq 1 ]; then
            if [ $exit_code -eq 0 ]; then
                rm -f "$expected_file"
                echo "Updated: $base_name (now passes, removed expected file)"
            elif matches_pattern "$pattern"; then
                # Still matches: keep the stored pattern byte for byte, so a
                # deliberately relaxed pattern survives regeneration.
                echo "Kept:    $base_name"
            else
                echo "$output" | failure_reason | derive_pattern > "$expected_file"
                echo "Updated: $base_name — $(cat "$expected_file")"
            fi
            passed=$((passed + 1))
        elif [ $exit_code -eq 0 ]; then
            echo "ERR:  $base_name (expected failure matching /$pattern/ but test passed)"
            errors=$((errors + 1))
        elif matches_pattern "$pattern"; then
            echo "OK:   $base_name (expected failure)"
            passed=$((passed + 1))
        else
            echo "ERR:  $base_name (output does not match expected pattern /$pattern/)"
            # Always name what was produced instead, not just under --verbose. A
            # mismatch that only reproduces on the build host is otherwise
            # undiagnosable from the log, and each dry run costs hours.
            report_mismatch
            if [ $verbose -eq 1 ]; then
                echo "$output" | sed 's/^/  /'
            fi
            errors=$((errors + 1))
        fi
    else
        # No expected file → test should pass
        if [ $update -eq 1 ] && [ $exit_code -ne 0 ]; then
            # Test fails unexpectedly; record the failure as this front end's baseline.
            echo "$output" | failure_reason | derive_pattern > "$expected_file"
            echo "Created: $base_name — $(cat "$expected_file")"
            passed=$((passed + 1))
        elif [ $exit_code -eq 0 ]; then
            echo "OK:   $base_name"
            passed=$((passed + 1))
        else
            reason=$(echo "$output" | failure_reason)
            echo "ERR:  $base_name (expected pass but failed) — $reason"
            if [ $verbose -eq 1 ]; then
                echo "$output" | grep -v "backtrace:" | grep -v "^  [0-9]" | grep -v "^$" | sed 's/^/  /'
            fi
            errors=$((errors + 1))
        fi
    fi
done

echo ""
echo "Results: $passed passed, $skipped skipped, $errors errors"

# Report how far apart the two front ends are, by comparing the two expectation sets
# directly. Shrinking this number is the point of the V2 work.
#
# Unlike the analyze goldens, a case's expectation may be ABSENT (it passes), so the
# comparison runs over the corpus rather than over one directory's files: a case that
# fails under V1 and passes under V2 has a file in only one of the two sets. Cases V1
# does not run (the imported corpus) are left out: V1 has no expectation for them, and
# counting that as "V1 passes" would report every one of them as diverging.
if [ -n "$OTHER_DIR" ] && [ -d "$OTHER_DIR" ]; then
    diverging=0
    total=0
    state_of() {
        # pass | skip | the .expected pattern
        if [ -f "$1/${2}.skip" ]; then echo "skip"
        elif [ -f "$1/${2}.expected" ]; then cat "$1/${2}.expected"
        else echo "pass"
        fi
    }
    for test_file in "$TESTS_DIR"/test_*.py; do
        [ -f "$test_file" ] || continue
        base_name=$(basename "$test_file" .py)
        [ -f "$SCRIPT_DIR/expected_interpret/${base_name}.desired" ] && continue
        total=$((total + 1))
        if [ "$(state_of "$OTHER_DIR" "$base_name")" != "$(state_of "$EXPECTED_DIR" "$base_name")" ]; then
            diverging=$((diverging + 1))
        fi
    done
    echo ""
    echo "V1/V2 divergence: $diverging of $total case(s) differ between \
$(basename "$OTHER_DIR")/ and $(basename "$EXPECTED_DIR")/."
fi

[ "$errors" -eq 0 ]
