# Tuples have no constructor in `Any` — `tuple[T1, T2]` is IN but
# unrepresentable; needs ClassInstance encoding or new tag
"""
The `Any` datatype has no `from_tuple` constructor. Tuples are IN the
Frontend subset (`tuple[T1, T2, ...]` with explicit element types), but
there is no way to represent them in the tagged union.

This means:
- `(1, "hello")` cannot be constructed
- `t[0]` on a tuple cannot be modeled
- `len(t)` on a tuple cannot be modeled
- Functions returning tuples have no representation for the return value
- `divmod(a, b)` returns a tuple — unrepresentable

Uses ONLY confirmed-accepted constructs: tuple, int, str, function def.
"""
from typing import Tuple


def swap(a: int, b: int) -> Tuple[int, int]:
    return (b, a)


def min_max(a: int, b: int) -> Tuple[int, int]:
    if a <= b:
        return (a, b)
    return (b, a)


def split_at(xs: list[int], idx: int) -> Tuple[list[int], list[int]]:
    """Split list into (before_idx, from_idx_onward) — simplified."""
    # Can't actually slice in subset, so just return lengths as proxy
    left: list[int] = []
    right: list[int] = []
    i: int = 0
    for x in xs:
        if i < idx:
            left.append(x)
        else:
            right.append(x)
        i = i + 1
    return (left, right)


def use_tuple_elements() -> int:
    t: Tuple[int, int] = swap(3, 7)
    # Access elements by index
    first: int = t[0]
    second: int = t[1]
    return first + second


def tuple_len() -> int:
    t: Tuple[int, int, int] = (10, 20, 30)
    return len(t)


def main() -> None:
    # Swap
    s: Tuple[int, int] = swap(3, 7)
    assert s[0] == 7
    assert s[1] == 3

    # Min/max
    mm: Tuple[int, int] = min_max(5, 2)
    assert mm[0] == 2
    assert mm[1] == 5

    # Element access
    assert use_tuple_elements() == 10  # 7 + 3

    # Tuple length
    assert tuple_len() == 3

    # Split
    parts: Tuple[list[int], list[int]] = split_at([1, 2, 3, 4, 5], 3)
    assert len(parts[0]) == 3
    assert len(parts[1]) == 2

    print(s[0], s[1], tuple_len())


main()
