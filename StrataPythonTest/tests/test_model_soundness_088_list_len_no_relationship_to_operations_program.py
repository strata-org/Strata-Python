# `List_len` has no axioms connecting it to operations — `len(a + b) == len(a)
# + len(b)` unprovable; loop bounds unverifiable
"""
After `lst = lst + [x]`, the new list has length `len(lst) + 1`. After
`lst = lst + other`, the new list has length `len(lst) + len(other)`.
If List_len and List_concat (PAdd on lists) are both uninterpreted with
no connecting axioms, these relationships are unprovable. Loop bounds
that depend on list growth become unverifiable.
"""


def build_list(n: int) -> list[int]:
    result: list[int] = []
    i: int = 0
    while i < n:
        result = result + [i]
        i = i + 1
    # CPython: len(result) == n
    # Model: if no axiom connects concat to len, unprovable
    return result


def append_and_check(lst: list[int], x: int) -> bool:
    old_len: int = len(lst)
    lst = lst + [x]
    new_len: int = len(lst)
    # Must be provable: new_len == old_len + 1
    return new_len == old_len + 1


def concat_lengths(a: list[int], b: list[int]) -> bool:
    len_a: int = len(a)
    len_b: int = len(b)
    c: list[int] = a + b
    # Must be provable: len(c) == len(a) + len(b)
    return len(c) == len_a + len_b


def empty_list_len() -> bool:
    empty: list[int] = []
    return len(empty) == 0


def singleton_len(x: int) -> bool:
    single: list[int] = [x]
    return len(single) == 1


def main() -> None:
    # Build list: length should equal n
    built: list[int] = build_list(5)
    assert len(built) == 5

    # Append increases length by 1
    assert append_and_check([1, 2, 3], 4) == True

    # Concat: lengths add
    assert concat_lengths([1, 2], [3, 4, 5]) == True

    # Empty list has length 0
    assert empty_list_len() == True

    # Singleton has length 1
    assert singleton_len(42) == True

    # Length is non-negative
    xs: list[int] = [10, 20, 30]
    assert len(xs) >= 0

    print(len(built), append_and_check([1, 2], 3), concat_lengths([1], [2, 3]))


main()
