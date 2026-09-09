# `int()` conversion maps to `to_int_any` which is never defined in the
# prelude; result is Hole
"""
The translator maps `int(x)` to a call to `to_int_any`, but this function
is never defined in the prelude. The call becomes a Hole (unconstrained Any),
so int() conversion produces an arbitrary value instead of truncation-toward-zero.
"""


def float_to_int(x: float) -> int:
    return int(x)


def clamp_to_int(x: float) -> int:
    # Common pattern: convert float result to int
    result: int = int(x * 10.0)
    return result


def main() -> None:
    # CPython: int(3.7) = 3 (truncate toward zero)
    a: int = float_to_int(3.7)
    assert a == 3

    # CPython: int(-3.7) = -3 (truncate toward zero, NOT floor)
    b: int = float_to_int(-3.7)
    assert b == -3

    # CPython: int(0.9) = 0
    c: int = float_to_int(0.9)
    assert c == 0

    # Laurel: all three are unconstrained (Hole), assertions unprovable
    print(a, b, c)


main()
