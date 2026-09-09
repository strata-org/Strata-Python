# List element assignment (`lst[i] = v`) needs `List_set` — cons-list requires
# full rebuild and variable rebinding
"""
`lst[i] = value` assigns a new value to an existing list index. In
CPython this mutates the list in place. In the value model (ListAny is
a cons-list), this requires creating a NEW list with the element at
position i replaced. The model needs a `List_set` operation that
rebuilds the cons-list. If it doesn't exist, list element assignment
either fails or produces Hole.
"""


def replace_at(lst: list[int], i: int, val: int) -> list[int]:
    lst[i] = val
    return lst


def swap(lst: list[int], i: int, j: int) -> list[int]:
    tmp: int = lst[i]
    lst[i] = lst[j]
    lst[j] = tmp
    return lst


def zero_negatives(lst: list[int]) -> list[int]:
    i: int = 0
    while i < len(lst):
        if lst[i] < 0:
            lst[i] = 0
        i = i + 1
    return lst


def main() -> None:
    # Basic element assignment
    data: list[int] = [10, 20, 30, 40]
    data[1] = 99
    assert data == [10, 99, 30, 40]

    # Replace at index
    result: list[int] = replace_at([1, 2, 3], 0, 100)
    assert result == [100, 2, 3]

    # Swap two elements
    swapped: list[int] = swap([1, 2, 3, 4], 0, 3)
    assert swapped == [4, 2, 3, 1]

    # Zero out negatives
    cleaned: list[int] = zero_negatives([5, -3, 7, -1, 2])
    assert cleaned == [5, 0, 7, 0, 2]

    # Assignment doesn't change length
    xs: list[int] = [1, 2, 3]
    xs[2] = 99
    assert len(xs) == 3

    print(data, swapped)


main()
