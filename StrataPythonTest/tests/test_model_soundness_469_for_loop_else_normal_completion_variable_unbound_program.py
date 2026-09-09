# For/else variable merge — variable assigned in else clause AND loop body has
# different values on break vs normal path; model must emit phi-node
# `ite(broke, body_val, else_val)` at join
"""
FOR-LOOP ELSE CLAUSE SETS VARIABLE — BREAK PATH LEAVES IT UNBOUND

The subset allows:
  - for/else (IN)
  - break (IN)
  - Variable assignment in branches (IN)

The NOVEL gap: a variable assigned ONLY in the else clause is unbound
on the break path. CPython raises NameError (or the variable holds
whatever was assigned before). The model, if it merges both paths
without tracking definite assignment per-path, may:
  1. Assume the variable always has the else-clause value (UNSOUND: over-proves)
  2. Leave it as Hole (correct but different from CPython's NameError)

The critical case: the variable is used AFTER the for/else block.
On the break path, CPython would raise NameError (if never assigned before)
or retain a prior value. The model must either:
  - Reject programs that use else-assigned variables after the block
  - Track definite assignment per control-flow path

This is DISTINCT from:
  - Finding 065 (for/else break semantics) — that's about WHEN else runs
  - Finding 330 (conditional break accumulator) — that's about break-flag
  - Finding 410 (break vs default merge) — that's about loop variable value
  - Finding 456 (else skipped on exception) — that's about exception path

THIS finding is about a VARIABLE that only exists on one path.
"""


def find_or_default(xs: list[int], target: int) -> int:
    """Find target in list, return index or -1.
    
    CPython: if target found, returns index (break path, 'result' from break)
             if not found, else runs, returns -1
    Model risk: 'result' may be assumed to always be -1 (else value)
                OR may be Hole on break path
    """
    for i in range(len(xs)):
        if xs[i] == target:
            result: int = i
            break
    else:
        result = -1
    return result


def search_with_flag(data: list[int], threshold: int) -> str:
    """Search sets a flag variable only in else clause.
    
    CPython: 'status' is "found" on break, "not_found" on else
    Model: if else-path variable leaks to break-path, status is always "not_found"
    """
    status: str = "unknown"
    for x in data:
        if x > threshold:
            status = "found"
            break
    else:
        status = "not_found"
    # CPython: status depends on which path was taken
    # Model: if translator doesn't properly handle for/else merge,
    #   status may be "not_found" on BOTH paths (else dominates)
    return status


def accumulate_then_else_resets(values: list[int]) -> int:
    """Accumulator modified in loop body AND else clause.
    
    The else clause RESETS the accumulator. If break exits early,
    the accumulated value is preserved. If loop completes normally,
    else resets to 0.
    
    CPython: break path returns partial sum; normal path returns 0
    Model risk: if else-clause assignment dominates, always returns 0
    """
    total: int = 0
    for v in values:
        total += v
        if total > 100:
            break
    else:
        total = 0  # Reset on normal completion
    return total


def main() -> None:
    # Test 1: find_or_default
    xs: list[int] = [10, 20, 30, 40, 50]
    idx: int = find_or_default(xs, 30)
    assert idx == 2  # CPython: found at index 2 (break path)
    # Model risk: if else dominates, idx == -1 (WRONG)

    idx2: int = find_or_default(xs, 99)
    assert idx2 == -1  # CPython: not found, else runs

    # Test 2: search_with_flag
    data: list[int] = [1, 2, 3, 200, 5]
    s: str = search_with_flag(data, 100)
    assert s == "found"  # CPython: 200 > 100, break taken
    # Model risk: if else dominates, s == "not_found" (WRONG)

    # Test 3: accumulate_then_else_resets
    vals: list[int] = [10, 20, 30, 50, 60]
    # total goes: 10, 30, 60, 110 > 100 → break
    r: int = accumulate_then_else_resets(vals)
    assert r == 110  # CPython: break preserves total=110
    # Model risk: else dominates → r == 0 (WRONG)

    short: list[int] = [1, 2, 3]
    r2: int = accumulate_then_else_resets(short)
    assert r2 == 0  # CPython: loop completes, else resets to 0

    print("all assertions passed")


main()
