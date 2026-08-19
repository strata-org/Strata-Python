#!/bin/bash

# Usage: ./run_py_analyze.sh [--v2] [--update] [--filter <pattern>] [--vc-directory <dir>] [--pending] [--check-pending]

# Runs the analyzer on all test_*.py files and compares output to expected.
# With --v2, run the V2 front-end (pyAnalyzeV2) instead of V1 (pyAnalyzeLaurel)
# With --update, overwrite existing expected files with actual output
# With --filter <pattern>, only run tests whose name contains <pattern>
# With --vc-directory <dir>, store VCs in SMT-Lib format in <dir>
# With --pending, also run tests without expected files and report their status
# With --check-pending, run pending tests and FAIL if any now pass (for CI)
#
# Tests in pending/ may contain a '# strata-pending: soundness' marker to
# indicate known soundness bugs (assertions that are FALSE in Python but that
# Strata incorrectly verifies as valid).  These are expected to "pass" and
# are reported separately; they do NOT trigger a --check-pending failure.
#
# Each front-end has its own full set of goldens: expected_laurel/ holds the V2
# expectations and expected_laurel_v1/ the V1 ones.  See
# expected_laurel/README.md for why the sets sit at those paths.

set -eo pipefail

failed=0
update=0
pending=0
check_pending=0
v2=0
filter=""
vc_directory=""

while [ $# -gt 0 ]; do
    case "$1" in
        --update) update=1 ;;
        --filter) filter="$2"; shift ;;
        --vc-directory) vc_directory="$2"; shift ;;
        --pending) pending=1 ;;
        --check-pending) pending=1; check_pending=1 ;;
        --v2) v2=1 ;;
        laurel) ;; # accepted for backward compatibility
        *) echo "Unknown argument: $1"; exit 1 ;;
    esac
    shift
done

# Which front-end to run, and where its goldens live.  Presence of
# <expected_dir>/<name>.expected is what makes a test part of that front-end's
# analyze suite; the two sets are expected to cover the same tests.
if [ $v2 -eq 1 ]; then
    front_end="V2"
    analyzer_name="pyAnalyzeV2"
    expected_dir="expected_laurel"
    # The other front-end's goldens, used only to report the V1/V2 divergence.
    other_dir="expected_laurel_v1"
else
    front_end="V1"
    analyzer_name="pyAnalyzeLaurel"
    expected_dir="expected_laurel_v1"
    other_dir=""
fi

# Python interpreter. Prefer the one the build exported (PYTHON), which has
# strata_python importable; fall back to python3 for manual local runs.
python="${PYTHON:-python3}"

# Normalize unstable assertion-label IDs in analyzer output so it matches the
# golden .expected files (see normalize_labels.py). The compiled binary emits
# raw labels like `assert(556)`; the goldens store the normalized `assert(…)`.
normalize_labels() {
    "$python" normalize_labels.py
}

# Build the analyzer exe in the StrataPython package.
(cd .. && lake build "$analyzer_name")
analyzer="../.lake/build/bin/${analyzer_name}"

echo "Running the ${front_end} front-end (${analyzer_name})"

pending_total=0
pending_error=0
pending_imprecise=0
pending_pass=0
pending_soundness=0

for test_file in tests/test_*.py; do
    if [ -f "$test_file" ]; then
        base_name=$(basename "$test_file" .py)

        # Apply name filter if specified
        if [ -n "$filter" ] && [[ "$base_name" != *"$filter"* ]]; then
            continue
        fi

        ion_file="tests/${base_name}.python.st.ion"
        expected_file="${expected_dir}/${base_name}.expected"

        if [ -f "$expected_file" ]; then
            (cd ../Python/strata-python && "$python" -m strata_python.gen py_to_strata --dialect "dialects/Python.dialect.st.ion" "../../StrataPythonTest/$test_file" "../../StrataPythonTest/$ion_file") || {
                echo "ERROR: py_to_strata failed for $base_name"
                failed=1
                continue
            }

            # Check for per-file strata arguments (e.g. # strata-args: --check-mode bugFinding)
            extra_args=$(grep -m1 '^# strata-args:' "$test_file" | sed 's/^# strata-args://' || true)
            vc_flag=""
            [ -n "$vc_directory" ] && vc_flag="--vc-directory $vc_directory"
            # The analyzer exits non-zero when it finds verification failures,
            # which is expected — we compare its output against the golden file.
            # Suppress its exit code so pipefail doesn't abort the script, but
            # let normalize_labels failures propagate.
            output=$({ "$analyzer" $extra_args $vc_flag "$ion_file" || true; } | normalize_labels)

            if [ $update -eq 1 ]; then
                echo "$output" > "$expected_file"
                echo "Updated: $expected_file"
            elif ! echo "$output" | diff -q "$expected_file" - > /dev/null; then
                echo "ERROR: Analysis output for $base_name does not match $expected_file"
                echo "$output" | diff "$expected_file" - || true
                failed=1
            else
                echo "Test passed: " $base_name
            fi

            # Check user_errors.txt if a .user_errors.expected file exists
            user_errors_expected="${expected_dir}/${base_name}.user_errors.expected"
            user_errors_file="user_errors.txt"
            if [ $update -eq 1 ] && [ -f "$user_errors_file" ]; then
                cp "$user_errors_file" "$user_errors_expected"
                echo "Updated: $user_errors_expected"
                rm -f "$user_errors_file"
            elif [ $update -eq 1 ] && [ -f "$user_errors_expected" ]; then
                # This front-end no longer emits user errors here; drop the stale
                # golden so --update fully regenerates the set rather than leaving
                # a file that the next check run would fail on.
                rm -f "$user_errors_expected"
                echo "Removed (no user errors emitted): $user_errors_expected"
            elif [ -f "$user_errors_expected" ]; then
                if [ ! -f "$user_errors_file" ]; then
                    echo "ERROR: user_errors.txt not generated for $base_name"
                    failed=1
                elif ! diff -q "$user_errors_expected" "$user_errors_file" > /dev/null; then
                    echo "ERROR: user_errors.txt content for $base_name does not match $user_errors_expected"
                    diff "$user_errors_expected" "$user_errors_file" || true
                    failed=1
                else
                    echo "Test passed:  ${base_name} (user_errors.txt)"
                fi
            fi
            rm -f "$user_errors_file"
        fi
    fi
done

# --- --metrics integration test ---
# Run one test file with --metrics and validate the JSONL output.
metrics_test_file=$(ls tests/test_*.py 2>/dev/null | head -1 || true)
if [ -n "$metrics_test_file" ] && [ -z "$filter" ]; then
    metrics_base=$(basename "$metrics_test_file" .py)
    metrics_ion="tests/${metrics_base}.python.st.ion"
    metrics_out=$(mktemp)
    # Ion file should already exist from the loop above
    if [ -f "$metrics_ion" ]; then
        ("$analyzer" --metrics "$metrics_out" "${metrics_ion}" 2>/dev/null) || true
        if [ ! -s "$metrics_out" ]; then
            echo "ERROR: --metrics file is empty for $metrics_base"
            failed=1
        else
            bad_lines=0
            while IFS= read -r line; do
                [ -z "$line" ] && continue
                if ! echo "$line" | python3 -c "import sys,json; d=json.load(sys.stdin); assert 'type' in d" 2>/dev/null; then
                    echo "ERROR: --metrics invalid JSON line: $line"
                    bad_lines=$((bad_lines + 1))
                fi
            done < "$metrics_out"
            # Check that an outcome record exists
            if ! grep -q '"outcome"' "$metrics_out"; then
                echo "ERROR: --metrics missing outcome record for $metrics_base"
                failed=1
            elif [ $bad_lines -gt 0 ]; then
                echo "ERROR: --metrics has $bad_lines invalid lines for $metrics_base"
                failed=1
            else
                echo "Test passed:  --metrics JSONL ($metrics_base)"
            fi
        fi
    fi
    rm -f "$metrics_out"
fi

if [ $pending -eq 1 ]; then
    for test_file in tests/pending/test_*.py; do
        [ -f "$test_file" ] || continue
        base_name=$(basename "$test_file" .py)

        if [ -n "$filter" ] && [[ "$base_name" != *"$filter"* ]]; then
            continue
        fi

        pending_total=$((pending_total + 1))
        ion_file="tests/pending/${base_name}.python.st.ion"

        parse_output=$(cd ../Python/strata-python && "$python" -m strata_python.gen py_to_strata --dialect "dialects/Python.dialect.st.ion" "../../StrataPythonTest/$test_file" "../../StrataPythonTest/$ion_file" 2>&1) && parse_exit=0 || parse_exit=$?

        if [ $parse_exit -ne 0 ]; then
            echo "Pending (parse error):    $base_name"
            pending_error=$((pending_error + 1))
            rm -f "user_errors.txt"
            continue
        fi

        extra_args=$(grep -m1 '^# strata-args:' "$test_file" | sed 's/^# strata-args://' || true)
        vc_flag=""
        [ -n "$vc_directory" ] && vc_flag="--vc-directory $vc_directory"
        output=$(timeout 20 "$analyzer" $extra_args $vc_flag "${ion_file}" 2>&1) && exit_code=0 || exit_code=$?

        if [ $exit_code -ne 0 ] || echo "$output" | grep -q "error\|Error\|ERROR\|panic\|PANIC"; then
            echo "Pending (analysis error): $base_name"
            pending_error=$((pending_error + 1))
        elif echo "$output" | grep -qE '[1-9][0-9]* (failed|inconclusive)'; then
            echo "Pending (imprecise):      $base_name"
            pending_imprecise=$((pending_imprecise + 1))
        elif grep -q '^# strata-pending: soundness' "$test_file"; then
            echo "Pending (soundness):      $base_name"
            pending_soundness=$((pending_soundness + 1))
        else
            echo "Pending (pass):           $base_name"
            pending_pass=$((pending_pass + 1))
        fi
        rm -f "../../user_errors.txt"
    done

    if [ $pending_total -gt 0 ]; then
        echo ""
        echo "Pending (${front_end}): $pending_total ($pending_error error, $pending_imprecise imprecise, $pending_soundness soundness, $pending_pass pass)"
    fi
    # Promotion out of tests/pending/ is gated on V1, the shipping front-end, so
    # a pending test that happens to pass under V2 must not fail the build.
    if [ $check_pending -eq 1 ] && [ $pending_pass -gt 0 ]; then
        echo ""
        if [ $v2 -eq 1 ]; then
            echo "NOTE: $pending_pass pending test(s) pass under the V2 front-end. Not a failure — promotion out of tests/pending/ is decided by the V1 run."
        else
            echo "ERROR: $pending_pass pending test(s) now pass. Move them from tests/pending/ to tests/ and generate expected files with --update."
            failed=1
        fi
    fi
fi

# Report how far apart the two front-ends are, by comparing the two golden sets
# directly.  Shrinking this number is the point of the V2 work.
if [ -n "$other_dir" ] && [ -d "$other_dir" ]; then
    diverging=0
    total=0
    for golden in "$expected_dir"/*.expected; do
        case "$golden" in *.user_errors.expected) continue ;; esac
        total=$((total + 1))
        if ! diff -q "${other_dir}/$(basename "$golden")" "$golden" > /dev/null 2>&1; then
            diverging=$((diverging + 1))
        fi
    done
    echo ""
    echo "V1/V2 divergence: $diverging of $total golden(s) differ between $other_dir/ and $expected_dir/."
fi

exit $failed
