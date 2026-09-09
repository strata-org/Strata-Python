# `sum()`, `min()`, `max()`, `abs()` builtins IN but no model — abs is trivial
# conditional; min/max are conditionals; sum needs recursive axiom
"""
The subset says `list.count(x)` and `list.index(x)` are "may grow."
But `len()`, `min()`, `max()`, `sum()` ARE in the subset.

`sum()` on a list of ints has no model (finding 026). But it's IN.
This finding tests `sum()` specifically — it must return the sum of
elements, with `sum([]) == 0`.

Similarly, `min()` and `max()` on lists must return the smallest/largest
element. These are IN but have no Laurel model.

Uses ONLY confirmed-accepted constructs: sum, min, max, abs, list, int.
"""


def sum_of_list(xs: list[int]) -> int:
    return sum(xs)


def sum_empty() -> int:
    return sum([])  # 0


def min_of_list(xs: list[int]) -> int:
    return min(xs)


def max_of_list(xs: list[int]) -> int:
    return max(xs)


def abs_value(x: int) -> int:
    return abs(x)


def range_width(xs: list[int]) -> int:
    """max - min = range width."""
    return max(xs) - min(xs)


def sum_of_absolutes(xs: list[int]) -> int:
    total: int = 0
    for x in xs:
        total = total + abs(x)
    return total


def clamp(x: int, lo: int, hi: int) -> int:
    return max(lo, min(x, hi))


def main() -> None:
    assert sum_of_list([1, 2, 3, 4, 5]) == 15
    assert sum_empty() == 0
    assert min_of_list([3, 1, 4, 1, 5]) == 1
    assert max_of_list([3, 1, 4, 1, 5]) == 5
    assert abs_value(-7) == 7
    assert abs_value(7) == 7
    assert range_width([3, 1, 4, 1, 5]) == 4
    assert sum_of_absolutes([-1, 2, -3, 4]) == 10
    assert clamp(5, 0, 10) == 5
    assert clamp(-5, 0, 10) == 0
    assert clamp(15, 0, 10) == 10

    print(sum_of_list([1, 2, 3]), min_of_list([5, 2, 8]),
          clamp(15, 0, 10))


main()
