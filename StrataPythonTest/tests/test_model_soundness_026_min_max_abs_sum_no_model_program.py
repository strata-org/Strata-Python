# `min()`, `max()`, `abs()`, `sum()` builtins are IN but have no Laurel model;
# results are unconstrained Hole
"""
The builtins min(), max(), abs(), sum() are explicitly IN the Frontend subset
but have no Laurel model. Calls to these functions produce unconstrained
Hole values, making any assertion about their results unprovable.
"""


def clamp(value: int, lo: int, hi: int) -> int:
    return max(lo, min(value, hi))


def absolute_diff(a: int, b: int) -> int:
    return abs(a - b)


def total(xs: list[int]) -> int:
    return sum(xs)


def main() -> None:
    # max/min
    c: int = clamp(15, 0, 10)
    assert c == 10

    c2: int = clamp(-5, 0, 10)
    assert c2 == 0

    # abs
    d: int = absolute_diff(3, 7)
    assert d == 4

    e: int = abs(-42)
    assert e == 42

    # sum
    s: int = total([1, 2, 3, 4])
    assert s == 10

    print(c, c2, d, e, s)


main()
