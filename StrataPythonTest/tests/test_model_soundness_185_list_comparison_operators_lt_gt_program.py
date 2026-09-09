# List ordering (`<`, `>`, `<=`, `>=`) — no `List_lt` for lexicographic
# comparison; `PLt(from_ListAny, from_ListAny)` falls to Hole
"""
Python lists support ordering comparisons: `<`, `>`, `<=`, `>=`.
Comparison is LEXICOGRAPHIC: compare element by element, first
difference determines the result. If one list is a prefix of the
other, the shorter list is "less than."

[1, 2, 3] < [1, 2, 4]  → True (first difference at index 2: 3 < 4)
[1, 2] < [1, 2, 3]     → True (prefix is less)
[1, 2, 3] < [1, 2, 3]  → False (equal)
[] < [1]                → True (empty is less than non-empty)

The model's `PEq` on lists uses structural equality (finding 040/091).
But `PLt` on lists likely has NO implementation at all — there's no
`List_lt` in the prelude.

Uses ONLY confirmed-accepted constructs: list, int, comparison, function def.
"""


def list_less_than(a: list[int], b: list[int]) -> bool:
    return a < b


def list_less_equal(a: list[int], b: list[int]) -> bool:
    return a <= b


def list_greater_than(a: list[int], b: list[int]) -> bool:
    return a > b


def find_min_list(lists: list[list[int]]) -> list[int]:
    """Find the lexicographically smallest list."""
    if len(lists) == 0:
        return []
    result: list[int] = lists[0]
    i: int = 1
    while i < len(lists):
        if lists[i] < result:
            result = lists[i]
        i = i + 1
    return result


def is_sorted_lists(lists: list[list[int]]) -> bool:
    """Check if a list of lists is in sorted order."""
    i: int = 0
    while i < len(lists) - 1:
        if lists[i] > lists[i + 1]:
            return False
        i = i + 1
    return True


def main() -> None:
    # Basic lexicographic comparison
    assert list_less_than([1, 2, 3], [1, 2, 4]) == True
    assert list_less_than([1, 2, 4], [1, 2, 3]) == False
    assert list_less_than([1, 2, 3], [1, 2, 3]) == False

    # Prefix comparison
    assert list_less_than([1, 2], [1, 2, 3]) == True
    assert list_less_than([1, 2, 3], [1, 2]) == False

    # Empty list
    assert list_less_than([], [1]) == True
    assert list_less_than([1], []) == False
    assert list_less_than([], []) == False

    # Less-equal
    assert list_less_equal([1, 2], [1, 2]) == True
    assert list_less_equal([1, 2], [1, 3]) == True

    # Greater-than
    assert list_greater_than([2, 1], [1, 9]) == True

    # Find min
    assert find_min_list([[3, 1], [1, 5], [2, 0]]) == [1, 5]

    # Is sorted
    assert is_sorted_lists([[1], [1, 2], [2]]) == True
    assert is_sorted_lists([[2], [1]]) == False

    print(list_less_than([1, 2], [1, 3]),
          find_min_list([[3], [1], [2]]),
          is_sorted_lists([[1], [2], [3]]))


main()
