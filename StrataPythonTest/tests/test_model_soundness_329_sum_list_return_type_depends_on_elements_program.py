# `sum()` return type depends on element type — `sum([1.0,2.0])` returns
# float; model returns Hole; sum([]) = 0 not error
"""
sum() return type depends on element type — sum([1.0, 2.0]) returns float.

In CPython:
  sum([1, 2, 3])       → 6     (int)
  sum([1.0, 2.0, 3.0]) → 6.0   (float)
  sum([1, 2.0, 3])     → 6.0   (float — int promoted)
  sum([])              → 0     (int — default start value)
  sum([], 0.0)         → 0.0   (float — explicit start)

Finding 026/228 note sum() has no model (Hole). This finding
specifically demonstrates the RETURN TYPE issue: sum() on a list
of floats must return from_float, not from_int. The model must
dispatch on element types to determine the result tag.

Additionally, sum([]) returns 0 (the default start value), not
an error. This differs from min([])/max([]) which raise ValueError.

Uses ONLY confirmed-accepted constructs: sum, list, float, int, type checking.
"""


def sum_ints(xs: list[int]) -> int:
    """sum() on int list returns int."""
    return sum(xs)
    # CPython: sum([1,2,3]) = 6 (int)
    # Model: Hole


def sum_floats(xs: list[float]) -> float:
    """sum() on float list returns float."""
    return sum(xs)
    # CPython: sum([1.0, 2.0, 3.0]) = 6.0 (float)
    # Model: Hole


def sum_empty_int() -> int:
    """sum([]) returns 0 (int), not an error."""
    xs: list[int] = []
    return sum(xs)
    # CPython: 0 (default start value)
    # Model: Hole — but should be from_int(0)
    # Note: unlike min([]) which raises ValueError


def sum_single(x: float) -> float:
    """sum of single-element list."""
    return sum([x])
    # CPython: x itself (as float)
    # Model: Hole


def sum_in_average(xs: list[int]) -> float:
    """Common pattern: sum(xs) / len(xs) for average."""
    if len(xs) == 0:
        return 0.0
    return sum(xs) / len(xs)
    # CPython: sum returns int, / returns float
    # Model: Hole / len(xs) → Hole (or exception if Hole in division)


def sum_postcondition(xs: list[int]) -> bool:
    """sum([a, b]) == a + b — basic postcondition unprovable."""
    a: int = 3
    b: int = 7
    return sum([a, b]) == a + b
    # CPython: True (sum([3,7]) == 10 == 3+7)
    # Model: Hole == 10 → unknown


def main() -> None:
    assert sum_ints([1, 2, 3]) == 6
    assert sum_floats([1.0, 2.0, 3.0]) == 6.0
    assert sum_empty_int() == 0
    assert sum_single(3.14) == 3.14
    assert sum_in_average([2, 4, 6]) == 4.0
    assert sum_postcondition([3, 7]) == True
