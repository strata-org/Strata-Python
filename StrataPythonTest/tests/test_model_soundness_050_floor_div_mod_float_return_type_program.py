# `//` and `%` on floats return `float`, not `int` — PFloorDiv/PMod likely
# missing float cases or returning wrong type tag
"""
Python's `//` (floor division) returns an int when both operands are int,
but returns a float when either operand is float. Similarly, `%` returns
float for float operands. The Laurel encoding's PFloorDiv and PMod likely
always return from_int (since they model integer division), but
`7.0 // 2.0` must return `3.0` (a float), not `3` (an int).
"""


def float_floor_div(a: float, b: float) -> float:
    return a // b


def mixed_floor_div(a: int, b: float) -> float:
    return a // b


def float_mod(a: float, b: float) -> float:
    return a % b


def main() -> None:
    # float // float -> float
    r1: float = float_floor_div(7.0, 2.0)
    assert r1 == 3.0
    # The TYPE matters: r1 is float, not int
    # isinstance(r1, float) == True in CPython

    # int // float -> float
    r2: float = mixed_floor_div(7, 2.0)
    assert r2 == 3.0

    # float % float -> float
    r3: float = float_mod(7.0, 2.0)
    assert r3 == 1.0

    # Negative case: float // float with negative
    r4: float = float_floor_div(-7.0, 2.0)
    assert r4 == -4.0  # floor division rounds toward -inf

    print(r1, r2, r3, r4)


main()
