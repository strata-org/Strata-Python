# List slicing (`lst[a:b]`) has no model — `List_get` handles single elements,
# no `List_slice` for sublists
"""
List slicing (`lst[a:b]`) creates a new list containing elements from
index a to b-1. The ListAny cons-list model has no slice operation —
List_get retrieves a single element by index. There is no List_slice
that extracts a sublist. The result is either Hole (uninterpreted) or
a type error (slice object not handled by Any_get!).
"""


def first_n(xs: list[int], n: int) -> list[int]:
    return xs[:n]


def last_n(xs: list[int], n: int) -> list[int]:
    return xs[len(xs) - n:]


def middle(xs: list[int]) -> list[int]:
    return xs[1:len(xs) - 1]


def split_at(xs: list[int], i: int) -> list[int]:
    left: list[int] = xs[:i]
    right: list[int] = xs[i:]
    return left + right  # should reconstruct original


def main() -> None:
    data: list[int] = [10, 20, 30, 40, 50]

    # Basic slicing
    assert first_n(data, 3) == [10, 20, 30]
    assert last_n(data, 2) == [40, 50]
    assert middle(data) == [20, 30, 40]

    # Slice + concatenation reconstructs original
    assert split_at(data, 2) == [10, 20, 30, 40, 50]

    # Empty slices
    assert first_n(data, 0) == []
    assert data[3:3] == []

    # Slice beyond bounds (no error — Python clamps)
    assert data[2:100] == [30, 40, 50]
    assert data[100:200] == []

    print(first_n(data, 3), middle(data))


main()
