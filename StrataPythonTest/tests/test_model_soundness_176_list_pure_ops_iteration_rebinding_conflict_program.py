# Pure list iteration vs body rebinding — `for x in xs` must snapshot xs at
# entry; if body rebinds xs, iteration uses stale/wrong list
"""
Lists are pure (cons-list). `for x in lst` iterates over the list.
But if the loop body rebinds `lst` (e.g., `lst = lst + [x]`), the
iteration must use the ORIGINAL list, not the rebound one.

In CPython, `for x in lst` creates an iterator over the list object
at loop entry. Reassigning `lst` in the body doesn't affect iteration
because the iterator holds a reference to the original object.

Under value semantics with pure lists, if the translator re-reads `lst`
each iteration (because it's a variable, not a snapshot), reassignment
in the body changes what's being iterated — WRONG.

Finding 031 noted this. This finding provides concrete programs showing
the interaction between pure-list rebinding and iteration.

Uses ONLY confirmed-accepted constructs: for, list, int, function def.
"""


def iterate_while_rebinding(xs: list[int]) -> int:
    """Reassign xs in loop body — iteration must use original."""
    total: int = 0
    for x in xs:
        total = total + x
        xs = []  # reassign xs — must NOT affect iteration
    return total


def collect_with_reassign(xs: list[int]) -> list[int]:
    """Build new list while iterating original."""
    result: list[int] = []
    for x in xs:
        result = result + [x * 2]
        # result grows each iteration, but we're iterating xs, not result
    return result


def filter_positive(xs: list[int]) -> list[int]:
    """Filter pattern — builds new list from old."""
    result: list[int] = []
    for x in xs:
        if x > 0:
            result.append(x)
    return result


def sum_and_clear(xs: list[int]) -> int:
    """Sum elements, then 'clear' the variable — iteration unaffected."""
    total: int = 0
    for x in xs:
        total = total + x
    xs = []  # after loop — fine, iteration already done
    return total


def main() -> None:
    # Rebinding xs in body must not affect iteration
    assert iterate_while_rebinding([1, 2, 3]) == 6  # 1+2+3, not just 1
    assert iterate_while_rebinding([10, 20]) == 30

    # Collect with reassign
    assert collect_with_reassign([1, 2, 3]) == [2, 4, 6]

    # Filter
    assert filter_positive([-1, 2, -3, 4, -5]) == [2, 4]
    assert filter_positive([]) == []

    # Sum and clear
    assert sum_and_clear([5, 10, 15]) == 30

    print(iterate_while_rebinding([1, 2, 3]),
          collect_with_reassign([1, 2, 3]),
          filter_positive([-1, 2, -3, 4]))


main()
