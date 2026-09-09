# Nested for loops with same variable name — inner loop rebinds outer's
# variable; outer iteration must use separate internal state
"""
Nested for loops where the inner loop reuses the same variable name
as the outer loop. Python has no block scoping — the inner loop
REBINDS the outer loop variable, and after the inner loop exits,
the variable holds the last value from the INNER loop.

    for i in [1, 2, 3]:
        for i in [10, 20]:
            pass
        # i is now 20, NOT the outer iteration value

This is legal Python (no shadowing error). The Laurel model must
correctly handle that:
1. The inner loop overwrites the outer loop variable
2. After the inner loop, the outer loop's "current element" is lost
3. The outer loop's NEXT iteration still proceeds correctly
   (because `for` in CPython uses an iterator object, not re-reading i)

Uses ONLY confirmed-accepted constructs: for loop, list, int.
"""


def inner_overwrites_outer(xs: list[int], ys: list[int]) -> int:
    """After inner loop, i holds last value from ys, not xs."""
    last_i: int = -1
    for i in xs:
        for i in ys:
            pass
        last_i = i  # i is last element of ys, not current xs element
    return last_i


def outer_loop_still_iterates(xs: list[int]) -> int:
    """Outer loop iterates all elements despite inner rebinding i."""
    count: int = 0
    for i in xs:
        for i in [100, 200]:
            pass
        count = count + 1
    # count should equal len(xs), not affected by inner loop
    return count


def accumulate_with_nested(matrix: list[list[int]]) -> int:
    """Sum all elements in a 2D list using same variable name."""
    total: int = 0
    for row in matrix:
        for item in row:
            total = total + item
    return total


def variable_value_after_nested() -> int:
    """The loop variable after nested loops holds inner's last value."""
    x: int = 0
    for x in [1, 2, 3]:
        for x in [10, 20, 30]:
            pass
    # x is 30 (last value of innermost loop's last iteration)
    return x


def main() -> None:
    # Inner loop overwrites outer variable
    assert inner_overwrites_outer([1, 2, 3], [10, 20]) == 20
    assert inner_overwrites_outer([5], [99]) == 99
    assert inner_overwrites_outer([1, 2], []) == 2  # inner never executes, i keeps outer value

    # Outer loop still iterates correctly
    assert outer_loop_still_iterates([1, 2, 3]) == 3
    assert outer_loop_still_iterates([10, 20, 30, 40, 50]) == 5
    assert outer_loop_still_iterates([]) == 0

    # 2D sum
    assert accumulate_with_nested([[1, 2], [3, 4], [5, 6]]) == 21

    # Variable value after nested
    assert variable_value_after_nested() == 30

    print("All nested loop variable tests pass")


main()
