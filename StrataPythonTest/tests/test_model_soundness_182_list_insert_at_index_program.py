# `list.insert(i, x)` — positional insertion in cons-list requires
# split+rejoin; needs `List_insert` with shift axioms
"""
`list.insert(i, x)` inserts element x at position i, shifting subsequent
elements right. Returns None. List grows by 1.

Under cons-list semantics:
- Insertion at index 0 is natural (cons)
- Insertion at arbitrary index requires splitting and rejoining
- The list variable must be rebound
- Return value is None

Key properties that must hold after insert:
- len(lst) increases by 1
- lst[i] == x (the inserted element)
- lst[j] == old_lst[j] for j < i (elements before unchanged)
- lst[j] == old_lst[j-1] for j > i (elements after shifted)

Uses ONLY confirmed-accepted constructs: list, insert, int, function def.
"""


def insert_at_beginning(xs: list[int], val: int) -> list[int]:
    xs.insert(0, val)
    return xs


def insert_at_end(xs: list[int], val: int) -> list[int]:
    xs.insert(len(xs), val)
    return xs


def insert_in_middle(xs: list[int], i: int, val: int) -> list[int]:
    xs.insert(i, val)
    return xs


def insert_returns_none() -> bool:
    xs: list[int] = [1, 2, 3]
    result = xs.insert(1, 99)
    return result is None


def sorted_insert(xs: list[int], val: int) -> list[int]:
    """Insert val into sorted position."""
    i: int = 0
    while i < len(xs) and xs[i] < val:
        i = i + 1
    xs.insert(i, val)
    return xs


def build_reversed(n: int) -> list[int]:
    """Build [n, n-1, ..., 1] by always inserting at front."""
    result: list[int] = []
    i: int = 1
    while i <= n:
        result.insert(0, i)
        i = i + 1
    return result


def main() -> None:
    # Insert at beginning
    assert insert_at_beginning([2, 3, 4], 1) == [1, 2, 3, 4]

    # Insert at end (same as append)
    assert insert_at_end([1, 2, 3], 4) == [1, 2, 3, 4]

    # Insert in middle
    assert insert_in_middle([1, 2, 4, 5], 2, 3) == [1, 2, 3, 4, 5]

    # Returns None
    assert insert_returns_none() == True

    # Sorted insert
    assert sorted_insert([1, 3, 5, 7], 4) == [1, 3, 4, 5, 7]
    assert sorted_insert([1, 3, 5], 0) == [0, 1, 3, 5]
    assert sorted_insert([1, 3, 5], 9) == [1, 3, 5, 9]

    # Build reversed
    assert build_reversed(4) == [4, 3, 2, 1]

    print(insert_at_beginning([2, 3], 1),
          sorted_insert([1, 3, 5], 4),
          build_reversed(3))


main()
