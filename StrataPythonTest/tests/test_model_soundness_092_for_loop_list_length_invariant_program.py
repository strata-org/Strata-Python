# `while i < len(lst)` loop — model must know len is invariant when lst is
# unmodified; needs loop invariant annotations
"""
When iterating `for x in lst` with a while-loop equivalent
`while i < len(lst)`, the loop bound `len(lst)` must remain stable
across iterations. Under value semantics (pure functions), if `lst`
is reassigned inside the loop (e.g., `lst = lst + [x]`), the length
changes. The model must correctly re-evaluate `len(lst)` each iteration.

But if `lst` is NOT reassigned, `len(lst)` is invariant. The model
must know this to prove termination (i increases, len(lst) is fixed).
"""


def sum_with_index(lst: list[int]) -> int:
    """Standard index-based iteration. len(lst) is loop-invariant."""
    total: int = 0
    i: int = 0
    while i < len(lst):
        total = total + lst[i]
        i = i + 1
    return total


def find_max(lst: list[int]) -> int:
    """Find maximum element. len(lst) is invariant."""
    if len(lst) == 0:
        return 0
    best: int = lst[0]
    i: int = 1
    while i < len(lst):
        if lst[i] > best:
            best = lst[i]
        i = i + 1
    return best


def growing_loop(n: int) -> list[int]:
    """Loop where list grows — len changes each iteration."""
    result: list[int] = []
    i: int = 0
    while i < n:
        result = result + [i * i]
        # len(result) increases each iteration
        # Loop terminates because i reaches n, not because of len
        i = i + 1
    return result


def count_above(lst: list[int], threshold: int) -> int:
    """Count elements above threshold. lst unchanged in loop."""
    count: int = 0
    i: int = 0
    while i < len(lst):
        if lst[i] > threshold:
            count = count + 1
        i = i + 1
    return count


def main() -> None:
    data: list[int] = [10, 20, 30, 40, 50]

    # Sum with index loop
    assert sum_with_index(data) == 150
    assert sum_with_index([]) == 0

    # Find max
    assert find_max(data) == 50
    assert find_max([3, 1, 4, 1, 5]) == 5

    # Growing loop
    squares: list[int] = growing_loop(5)
    assert squares == [0, 1, 4, 9, 16]
    assert len(squares) == 5

    # Count above
    assert count_above(data, 25) == 3  # 30, 40, 50

    print(sum_with_index(data), find_max(data), len(squares))


main()
