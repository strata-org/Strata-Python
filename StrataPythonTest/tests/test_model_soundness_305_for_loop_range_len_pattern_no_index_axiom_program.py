# `for i in range(len(lst)): lst[i]` — no axiom connecting range output to
# list bounds; index validity unprovable (false positive)
"""
FOR-LOOP OVER range(len(lst)): index variable has no connection to list bounds.

The pattern `for i in range(len(lst)): lst[i]` is extremely common.
It requires THREE things to be sound:
  1. range(n) produces values 0, 1, ..., n-1 (finding 161)
  2. len(lst) returns the list length (finding 088)
  3. The loop body can ASSUME 0 <= i < len(lst) — the INDEX VALIDITY axiom

The critical gap: even if range and len are individually modeled, the
COMPOSITION has no axiom connecting them. The solver sees:
  - i comes from range(len(lst))
  - lst[i] requires 0 <= i < len(lst)

But without an axiom stating "values produced by range(n) satisfy 0 <= v < n",
the precondition for lst[i] is UNPROVABLE. The verifier reports "cannot verify"
for a program that is obviously safe.

This is NOT about missing models for range or len individually — it's about
the LOOP INVARIANT that connects the iteration variable to the list bounds.

CPython: always safe (range never produces out-of-bounds index)
Model:   cannot prove lst[i] is safe — reports spurious "possible IndexError"
"""


def sum_by_index(lst: list[int]) -> int:
    """Sum using index-based access — requires i < len(lst)."""
    total: int = 0
    for i in range(len(lst)):
        total = total + lst[i]  # needs: 0 <= i < len(lst)
    return total


def find_max_index(lst: list[int]) -> int:
    """Find index of maximum element."""
    if len(lst) == 0:
        return -1
    max_idx: int = 0
    for i in range(len(lst)):
        if lst[i] > lst[max_idx]:  # needs: i and max_idx both valid
            max_idx = i
    return max_idx


def reverse_list(lst: list[int]) -> list[int]:
    """Reverse by index — needs len(lst)-1-i >= 0."""
    result: list[int] = []
    for i in range(len(lst)):
        result.append(lst[len(lst) - 1 - i])  # needs: 0 <= len-1-i < len
    return result


def pairwise_sum(a: list[int], b: list[int]) -> list[int]:
    """Element-wise sum of two same-length lists."""
    result: list[int] = []
    for i in range(len(a)):
        result.append(a[i] + b[i])  # needs: i < len(a) AND i < len(b)
    return result


def transform_in_place(lst: list[int]) -> list[int]:
    """Double each element by index."""
    for i in range(len(lst)):
        lst[i] = lst[i] * 2  # needs: i valid for both read and write
    return lst


def main() -> None:
    # Sum by index
    assert sum_by_index([1, 2, 3, 4]) == 10
    assert sum_by_index([]) == 0
    assert sum_by_index([5]) == 5

    # Find max index
    assert find_max_index([3, 7, 2, 9, 1]) == 3
    assert find_max_index([5]) == 0
    assert find_max_index([]) == -1

    # Reverse
    assert reverse_list([1, 2, 3]) == [3, 2, 1]
    assert reverse_list([]) == []
    assert reverse_list([7]) == [7]

    # Pairwise sum (assumes same length)
    assert pairwise_sum([1, 2, 3], [4, 5, 6]) == [5, 7, 9]
    assert pairwise_sum([], []) == []

    # Transform in place
    assert transform_in_place([1, 2, 3]) == [2, 4, 6]

    print(sum_by_index([1, 2, 3]), find_max_index([3, 7, 2]),
          reverse_list([1, 2, 3]))


main()
