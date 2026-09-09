# `for/else` clause — `else` runs only when no `break` was hit; model may
# always or never execute it
"""
Python's `for/else` construct: the `else` block runs ONLY if the loop
completes without hitting a `break`. If `break` is executed, the `else`
block is skipped. This is a control-flow subtlety that the model must
handle: the `else` clause is NOT simply "code after the loop" — it is
conditionally executed based on whether `break` was reached.
"""


def find_index(xs: list[int], target: int) -> int:
    """Return index of target, or -1 if not found."""
    i: int = 0
    for x in xs:
        if x == target:
            break
        i = i + 1
    else:
        # Only runs if loop completed without break (target not found)
        return -1
    # Only reaches here if break was hit (target found)
    return i


def has_negative(xs: list[int]) -> bool:
    for x in xs:
        if x < 0:
            break
    else:
        # No negative found — loop completed normally
        return False
    # break was hit — negative exists
    return True


def first_divisor(n: int, candidates: list[int]) -> int:
    """Find first element of candidates that divides n, or 0."""
    for c in candidates:
        if c != 0 and n % c == 0:
            break
    else:
        return 0
    return c


def main() -> None:
    # find_index: target found → break → else skipped → return index
    assert find_index([10, 20, 30, 40], 30) == 2

    # find_index: target not found → no break → else runs → return -1
    assert find_index([10, 20, 30, 40], 99) == -1

    # has_negative: negative exists → break → else skipped → True
    assert has_negative([1, -2, 3]) == True

    # has_negative: no negative → no break → else runs → False
    assert has_negative([1, 2, 3]) == False

    # first_divisor: divisor found
    assert first_divisor(12, [5, 4, 3]) == 4

    # first_divisor: no divisor found
    assert first_divisor(7, [2, 3, 4]) == 0

    print(find_index([10, 20, 30], 20), has_negative([1, -1]), first_divisor(12, [5, 4]))


main()
