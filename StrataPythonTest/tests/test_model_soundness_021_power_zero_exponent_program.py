# `**` operator (`PPow`) is uninterpreted; `0**0==1`, `x**0==1`, negative-base
# sign rules are all unprovable
"""
Python defines 0**0 == 1 and handles negative bases with odd/even exponents.
The Laurel PPow likely uses an uninterpreted function or SMT power that
may not match Python's specific edge-case definitions.
"""


def power_zero(base: int) -> int:
    # Python: any_int ** 0 == 1, including 0 ** 0 == 1
    return base ** 0


def negative_base_power(base: int, exp: int) -> int:
    # Python: (-2) ** 3 == -8, (-2) ** 2 == 4
    return base ** exp


def main() -> None:
    # 0 ** 0 is defined as 1 in Python (and in math.pow, int.__pow__)
    a: int = power_zero(0)
    assert a == 1

    # Any integer to the power 0 is 1
    b: int = power_zero(42)
    assert b == 1

    c: int = power_zero(-5)
    assert c == 1

    # Negative base with odd exponent: negative result
    d: int = negative_base_power(-2, 3)
    assert d == -8

    # Negative base with even exponent: positive result
    e: int = negative_base_power(-2, 4)
    assert e == 16

    # 1 ** anything == 1
    f: int = 1 ** 1000
    assert f == 1

    print(a, b, c, d, e, f)


main()
