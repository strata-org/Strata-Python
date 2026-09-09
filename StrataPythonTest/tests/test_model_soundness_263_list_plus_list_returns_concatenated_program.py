# `[1,2] + [3,4]` = [1,2,3,4] — PAdd has no list×list case; list concatenation
# returns Hole
"""
CPython results (concrete):
  [1, 2] + [3, 4] = [1, 2, 3, 4]
  [] + [1]         = [1]
  [1] + []         = [1]

Laurel model results:
  PAdd(from_ListAny([1,2]), from_ListAny([3,4])) = Hole (no list+list case)
"""


def concat_lists(a: list[int], b: list[int]) -> list[int]:
    return a + b


def prepend_element(x: int, xs: list[int]) -> list[int]:
    return [x] + xs


def append_element(xs: list[int], x: int) -> list[int]:
    return xs + [x]


def main() -> None:
    # CPython: [1,2] + [3,4] = [1,2,3,4]
    assert concat_lists([1, 2], [3, 4]) == [1, 2, 3, 4]
    # CPython: [] + [1] = [1]
    assert concat_lists([], [1]) == [1]
    # CPython: [1] + [] = [1]
    assert concat_lists([1], []) == [1]
    # CPython: [] + [] = []
    assert concat_lists([], []) == []

    # Prepend
    assert prepend_element(0, [1, 2, 3]) == [0, 1, 2, 3]

    # Append via concat
    assert append_element([1, 2], 3) == [1, 2, 3]

    print(concat_lists([1, 2], [3, 4]), prepend_element(0, [1, 2]),
          append_element([10], 20))


main()
