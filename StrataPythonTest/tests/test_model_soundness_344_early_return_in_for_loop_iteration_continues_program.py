# Early `return` inside for loop — if return doesn't terminate, loop continues
# and LAST match overwrites FIRST match
"""
EARLY RETURN INSIDE FOR LOOP — REMAINING ITERATIONS MUST NOT EXECUTE

CPython: `return` inside a for loop immediately exits the function.
         No further iterations execute. No code after the loop executes.

Model:   If `return` is translated as assignment to result variable
         WITHOUT making subsequent code unreachable (finding 052/165),
         the loop CONTINUES ITERATING after the "return."
         The final iteration's value overwrites the early return's value.

This is the INTERACTION between findings 052 (return doesn't terminate)
and for-loop translation. The loop body executes for ALL elements,
and the LAST iteration's return value wins — not the first match.
"""


def find_first_negative(xs: list[int]) -> int:
    """Return the first negative number, or 0 if none."""
    for x in xs:
        if x < 0:
            return x  # should exit immediately
    return 0


def find_index(xs: list[int], target: int) -> int:
    """Return index of first occurrence, or -1."""
    i: int = 0
    for x in xs:
        if x == target:
            return i  # should exit with current i
        i += 1
    return -1


def first_above_threshold(xs: list[int], threshold: int) -> int:
    """Return first element above threshold."""
    for x in xs:
        if x > threshold:
            return x
    return -1


def count_until_zero(xs: list[int]) -> int:
    """Count elements before the first zero."""
    count: int = 0
    for x in xs:
        if x == 0:
            return count  # return CURRENT count, not final
        count += 1
    return count


def main() -> None:
    # Test 1: first negative
    data: list[int] = [5, 3, -2, 7, -8, 1]
    result: int = find_first_negative(data)
    # CPython: -2 (first negative, exits immediately)
    # Model (if return doesn't terminate): -8 (LAST negative wins)
    assert result == -2

    # Test 2: find index
    idx: int = find_index([10, 20, 30, 20, 40], 20)
    # CPython: 1 (first occurrence)
    # Model: 3 (last occurrence, because loop continues)
    assert idx == 1

    # Test 3: first above threshold
    val: int = first_above_threshold([1, 5, 3, 8, 2, 9], 4)
    # CPython: 5 (first above 4)
    # Model: 9 (last above 4)
    assert val == 5

    # Test 4: count until zero
    c: int = count_until_zero([7, 3, 0, 5, 0, 2])
    # CPython: 2 (two elements before first zero)
    # Model: count keeps incrementing past the zero → wrong value
    assert c == 2

    print(result)
    print(idx)


main()
