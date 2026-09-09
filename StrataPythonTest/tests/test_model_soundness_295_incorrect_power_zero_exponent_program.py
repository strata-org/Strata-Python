# Incorrect `**` uninterpreted: CPython `5**0=1`, Model→Hole — PPow has no
# definition or axioms
"""
INCORRECT OPERATOR BEHAVIOR: ** (power) with zero exponent.

CPython: x ** 0 = 1 for ALL x (including 0**0 = 1)
Model:   PPow is uninterpreted → x ** 0 = Hole (unknown)

The model can't prove the most basic power identity: anything**0 == 1.
"""


def power_zero_exponent() -> list[int]:
    results: list[int] = []
    results.append(5 ** 0)     # CPython: 1
    results.append(0 ** 0)     # CPython: 1 (by convention)
    results.append((-3) ** 0)  # CPython: 1
    results.append(100 ** 0)   # CPython: 1
    return results


def power_basic() -> list[int]:
    results: list[int] = []
    results.append(2 ** 3)     # CPython: 8
    results.append(3 ** 2)     # CPython: 9
    results.append(2 ** 10)    # CPython: 1024
    return results


def power_one_exponent(x: int) -> int:
    return x ** 1  # always x


def main() -> None:
    # Zero exponent: always 1
    r: list[int] = power_zero_exponent()
    assert r == [1, 1, 1, 1]

    # Basic powers
    p: list[int] = power_basic()
    assert p[0] == 8
    assert p[1] == 9
    assert p[2] == 1024

    # x**1 == x
    assert power_one_exponent(7) == 7
    assert power_one_exponent(0) == 0

    print(r, p[0], power_one_exponent(7))


main()
