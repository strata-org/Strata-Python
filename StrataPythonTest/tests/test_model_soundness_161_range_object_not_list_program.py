# `range(start, stop, step)` iteration semantics — negative step needs
# reversed condition; stop exclusive; empty range when wrong direction
"""
`range(start, stop, step)` produces a range OBJECT, not a list.
In `for x in range(...)`, the translator must generate correct iteration
bounds. Key issues:

1. range(5) → 0,1,2,3,4 (stop exclusive)
2. range(2, 7) → 2,3,4,5,6
3. range(10, 0, -2) → 10,8,6,4,2 (negative step, stop exclusive)
4. range(5, 5) → empty (start == stop)
5. range(5, 3) → empty (start > stop with positive step)

The model must correctly compute iteration count and element values.
If it models range as a list literal, `len(range(n))` and indexing
semantics differ (range supports negative indexing, len, `in`).

Uses ONLY confirmed-accepted constructs: for, range, int, function def.
"""


def sum_range(n: int) -> int:
    total: int = 0
    for i in range(n):
        total = total + i
    return total


def sum_range_start_stop(start: int, stop: int) -> int:
    total: int = 0
    for i in range(start, stop):
        total = total + i
    return total


def countdown_sum(start: int, stop: int, step: int) -> int:
    """Sum elements of range(start, stop, step)."""
    total: int = 0
    for i in range(start, stop, step):
        total = total + i
    return total


def count_iterations(start: int, stop: int, step: int) -> int:
    """Count how many times the loop body executes."""
    count: int = 0
    for i in range(start, stop, step):
        count = count + 1
    return count


def range_stop_exclusive() -> bool:
    """range(5) does NOT include 5."""
    found_five: bool = False
    for i in range(5):
        if i == 5:
            found_five = True
    return found_five


def main() -> None:
    # Basic range(n)
    assert sum_range(5) == 10  # 0+1+2+3+4
    assert sum_range(0) == 0   # empty range
    assert sum_range(1) == 0   # just 0

    # range(start, stop)
    assert sum_range_start_stop(2, 5) == 9  # 2+3+4
    assert sum_range_start_stop(5, 5) == 0  # empty
    assert sum_range_start_stop(7, 3) == 0  # empty (start > stop)

    # Negative step
    assert countdown_sum(10, 0, -2) == 30  # 10+8+6+4+2
    assert countdown_sum(5, 0, -1) == 15   # 5+4+3+2+1
    assert countdown_sum(0, 5, -1) == 0    # empty (wrong direction)

    # Iteration count
    assert count_iterations(0, 10, 3) == 4   # 0,3,6,9
    assert count_iterations(0, 10, 10) == 1  # just 0
    assert count_iterations(0, 0, 1) == 0    # empty

    # Stop is exclusive
    assert range_stop_exclusive() == False

    print(sum_range(5), countdown_sum(10, 0, -2), count_iterations(0, 10, 3))


main()
