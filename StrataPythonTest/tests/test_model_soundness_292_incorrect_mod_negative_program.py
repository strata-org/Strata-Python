# Incorrect `%` negative: CPython `-7%3=2`, Model `-1` — SMT mod sign follows
# dividend instead of divisor
"""
INCORRECT OPERATOR BEHAVIOR: % on negative operands.

CPython: -7 % 3 = 2 (sign follows divisor)
Model:   -7 % 3 = -1 (SMT mod, sign follows dividend)

The model computes a value with the WRONG SIGN.
"""


def test_mod() -> list[int]:
    results: list[int] = []
    results.append(-7 % 3)    # CPython: 2,  Model: -1
    results.append(-1 % 3)    # CPython: 2,  Model: -1
    results.append(7 % -3)    # CPython: -2, Model: 1
    results.append(1 % -3)    # CPython: -2, Model: 1
    results.append(-10 % 4)   # CPython: 2,  Model: -2
    return results


def main() -> None:
    r: list[int] = test_mod()
    assert r == [2, 2, -2, -2, 2]
    print(r)


main()
