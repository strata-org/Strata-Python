# `break` must preserve loop variable value at break point — variable holds
# breaking iteration's value, not last or initial
"""
When `break` exits a for loop, the loop variable retains the value
from the iteration where `break` was executed. The model must ensure
that after a `break`:
1. The loop variable holds the value from the breaking iteration
2. The loop's `else` clause (if any) is NOT executed
3. Code after the loop sees the correct variable value

Combined with finding 054 (break/continue control flow), this tests
the INTERACTION between break and the loop variable's final value.

The critical pattern is:
    for i in range(n):
        if condition(i):
            break
    # i holds the value where condition was True

If the model doesn't correctly stop iteration at break, `i` will
hold the LAST value (n-1) instead of the breaking value.

Uses ONLY confirmed-accepted constructs: for, range, break, if, int, list.
"""


def find_first_above(xs: list[int], threshold: int) -> int:
    """Return first element above threshold, or -1."""
    result: int = -1
    for x in xs:
        if x > threshold:
            result = x
            break
    return result


def find_index_of(xs: list[int], target: int) -> int:
    """Return index of target in list, or -1."""
    idx: int = -1
    i: int = 0
    for x in xs:
        if x == target:
            idx = i
            break
        i = i + 1
    return idx


def break_preserves_loop_var() -> int:
    """Loop variable holds value at break point, not end of range."""
    i: int = 0
    for i in range(100):
        if i == 7:
            break
    # i should be 7, NOT 99
    return i


def break_in_nested_only_inner() -> int:
    """Break in inner loop doesn't affect outer loop."""
    outer_count: int = 0
    for a in range(5):
        for b in range(10):
            if b == 3:
                break
        # inner loop broke at b==3, outer continues
        outer_count = outer_count + 1
    # outer_count should be 5 (all outer iterations complete)
    return outer_count


def continue_skips_rest(xs: list[int]) -> int:
    """Continue skips rest of body; loop variable advances normally."""
    total: int = 0
    for x in xs:
        if x < 0:
            continue
        total = total + x
    return total


def break_with_accumulator(xs: list[int], limit: int) -> int:
    """Sum elements until sum exceeds limit, then break."""
    total: int = 0
    for x in xs:
        total = total + x
        if total > limit:
            break
    return total


def main() -> None:
    # Find first above threshold
    assert find_first_above([1, 5, 3, 8, 2], 4) == 5
    assert find_first_above([1, 2, 3], 10) == -1
    assert find_first_above([], 0) == -1

    # Find index
    assert find_index_of([10, 20, 30, 40], 30) == 2
    assert find_index_of([10, 20, 30], 99) == -1

    # Break preserves loop variable value
    assert break_preserves_loop_var() == 7

    # Nested break only affects inner
    assert break_in_nested_only_inner() == 5

    # Continue skips negatives
    assert continue_skips_rest([1, -2, 3, -4, 5]) == 9
    assert continue_skips_rest([-1, -2, -3]) == 0

    # Break with accumulator
    assert break_with_accumulator([10, 20, 30, 40], 25) == 30
    assert break_with_accumulator([1, 2, 3], 100) == 6  # never exceeds

    print("All break/continue index value tests pass")


main()
