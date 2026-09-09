# Comparison return type must be `from_bool` — if PLt returns `from_int(1)`
# instead, downstream bool checks fail
"""
Comparison operators (`<`, `>`, `<=`, `>=`, `==`, `!=`) must return
`from_bool(True)` or `from_bool(False)`. If PLt/PGt/etc. return
`from_int` (e.g., 0 or 1) instead of `from_bool`, subsequent boolean
operations on the result fail: `if` conditions expect `from_bool`,
`and`/`or` expect `from_bool`, etc.
"""


def is_positive(x: int) -> bool:
    return x > 0


def clamp(x: int, lo: int, hi: int) -> int:
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x


def both_positive(a: int, b: int) -> bool:
    # Result of > is used in `and` — must be from_bool
    return a > 0 and b > 0


def count_above(xs: list[int], threshold: int) -> int:
    count: int = 0
    for x in xs:
        if x > threshold:
            count = count + 1
    return count


def min_of_two(a: int, b: int) -> int:
    if a <= b:
        return a
    return b


def main() -> None:
    # Comparison returns bool
    assert is_positive(5) == True
    assert is_positive(-3) == False
    assert is_positive(0) == False

    # Comparison in if condition
    assert clamp(5, 0, 10) == 5
    assert clamp(-5, 0, 10) == 0
    assert clamp(15, 0, 10) == 10

    # Comparison result used in boolean expression
    assert both_positive(1, 2) == True
    assert both_positive(-1, 2) == False

    # Comparison in loop
    assert count_above([1, 5, 3, 7, 2], 3) == 2

    # <= comparison
    assert min_of_two(3, 5) == 3
    assert min_of_two(7, 2) == 2

    # Type of comparison result
    r: bool = (5 > 3)
    assert r == True
    assert type(r) == bool

    print(is_positive(5), clamp(15, 0, 10), count_above([1, 5, 3, 7], 3))


main()
