# Reflected dispatch: `int * list` — int.__mul__(list)→NotImplemented,
# list.__rmul__(int)→repeated list; model → Hole
"""
MISSING REFLECTED METHOD DISPATCH: int * list

CPython protocol:
  1. int.__mul__(list) → NotImplemented
  2. list.__rmul__(int) → repeated list ✓

Model: PMul(from_int(3), from_ListAny([1,2]))
  → match: no (from_int, from_ListAny) case
  → Hole

CPython result: [1, 2, 1, 2, 1, 2]
Model result:  Hole
"""


def int_times_list(n: int, xs: list[int]) -> list[int]:
    return n * xs


def list_times_int(xs: list[int], n: int) -> list[int]:
    return xs * n


def main() -> None:
    # CPython: 3 * [1, 2] = [1, 2, 1, 2, 1, 2] (via list.__rmul__)
    assert int_times_list(3, [1, 2]) == [1, 2, 1, 2, 1, 2]
    assert int_times_list(0, [1, 2]) == []
    assert int_times_list(1, [5]) == [5]

    # CPython: [1, 2] * 2 = [1, 2, 1, 2] (via list.__mul__)
    assert list_times_int([1, 2], 2) == [1, 2, 1, 2]
    assert list_times_int([1, 2], 0) == []

    print(int_times_list(3, [1, 2]), list_times_int([1, 2], 2))


main()
