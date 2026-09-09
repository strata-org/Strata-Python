# `continue` in nested loops — must target only innermost loop; single-flag or
# single-label encoding conflates loop levels
"""
CONTINUE in nested loops must target ONLY the innermost enclosing loop.

In CPython, `continue` skips the rest of the current iteration of the
INNERMOST loop only. The outer loop continues normally. If the model's
control flow encoding uses a single "skip" mechanism (e.g., a flag or
goto that doesn't distinguish loop levels), `continue` in an inner loop
may incorrectly skip the outer loop's iteration too.

    for i in range(3):
        for j in range(3):
            if j == 1:
                continue  # skips rest of INNER loop body only
            # ... this code runs for j=0 and j=2, not j=1
        # ... this code ALWAYS runs for each i (outer loop unaffected)

Similarly for while loops:
    while outer_cond:
        while inner_cond:
            if skip:
                continue  # only skips inner iteration
            inner_work()
        outer_work()  # always executes

This is distinct from:
- Finding 054 (break/continue may not work at all)
- Finding 307 (nested for loops variable rebinding)
- Finding 309 (break preserves loop variable)

This finding specifically tests that continue in an INNER loop does not
affect the OUTER loop's control flow.

Uses ONLY confirmed-accepted constructs: for, range, while, continue, if, int, list.
"""


def count_non_skipped_inner(n: int, skip_val: int) -> int:
    """Count iterations where inner continue does NOT fire."""
    total: int = 0
    i: int = 0
    while i < n:
        j: int = 0
        while j < n:
            if j == skip_val:
                j = j + 1
                continue  # skip THIS inner iteration only
            total = total + 1
            j = j + 1
        # Outer loop body continues normally after inner loop
        i = i + 1
    # CPython: n=3, skip_val=1 → inner runs 2 times per outer → 3*2=6
    # Model (if continue skips outer too): fewer iterations
    return total


def outer_accumulates_despite_inner_continue() -> int:
    """Outer loop accumulator must not be affected by inner continue."""
    outer_sum: int = 0
    for i in range(4):
        inner_count: int = 0
        for j in range(5):
            if j % 2 == 0:
                continue  # skip even j values in inner loop
            inner_count = inner_count + 1
        # inner_count should be 2 (j=1, j=3 — odd values only)
        # This line MUST execute for every i
        outer_sum = outer_sum + inner_count
    # CPython: 4 * 2 = 8
    # Model (if continue affects outer): outer_sum < 8
    return outer_sum


def continue_only_skips_rest_of_inner_body() -> list[int]:
    """Code AFTER continue in inner loop is skipped; outer code is not."""
    results: list[int] = []
    for i in range(3):
        for j in range(3):
            if j == 1:
                continue
            # This append only happens for j=0 and j=2
            results.append(i * 10 + j)
        # This is outer loop body — always executes
        # (no append here, but the loop continues)
    # CPython: [0, 2, 10, 12, 20, 22] (6 elements)
    # Model (if continue skips outer): fewer elements
    return results


def nested_while_continue() -> int:
    """While-in-while with continue in inner."""
    total: int = 0
    i: int = 0
    while i < 3:
        j: int = 0
        while j < 4:
            j = j + 1
            if j == 2:
                continue  # skip j==2, continue inner while
            total = total + 1
        # Outer body: i increments
        i = i + 1
    # Inner loop: j goes 1,2,3,4; continue skips j==2
    # So inner adds 3 per outer iteration (j=1,3,4)
    # Total: 3 * 3 = 9
    # Model (if continue breaks out of inner): total < 9
    return total


def continue_with_accumulator_after() -> int:
    """Code after the inner for loop must see correct inner state."""
    result: int = 0
    for i in range(3):
        skipped: int = 0
        for j in range(5):
            if j < 2:
                skipped = skipped + 1
                continue
            # Only j=2,3,4 reach here
            result = result + j
        # skipped should be 2 for each i (j=0, j=1 were skipped)
        result = result + skipped
    # Per outer iteration: result += (2+3+4) + 2 = 11
    # Total: 3 * 11 = 33
    # Model (if continue conflates loops): wrong total
    return result


def main() -> None:
    # Inner continue doesn't affect outer iteration count
    assert count_non_skipped_inner(3, 1) == 6

    # Outer accumulator unaffected by inner continue
    assert outer_accumulates_despite_inner_continue() == 8

    # Continue only skips rest of inner body
    expected: list[int] = [0, 2, 10, 12, 20, 22]
    actual: list[int] = continue_only_skips_rest_of_inner_body()
    assert len(actual) == 6
    assert actual[0] == 0
    assert actual[1] == 2
    assert actual[2] == 10
    assert actual[5] == 22

    # Nested while with continue
    assert nested_while_continue() == 9

    # Continue with accumulator
    assert continue_with_accumulator_after() == 33

    print("All nested continue tests pass")


main()
