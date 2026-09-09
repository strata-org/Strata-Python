# `%` sign follows divisor — CPython: `-7%3 = 2`; SMT `mod`: `-7 mod 3 = -1`;
# model computes WRONG VALUE
"""
CPython: -7 % 3 → 2 (sign follows DIVISOR, result is non-negative when divisor > 0)
Model:   PMod uses SMT `mod` → -7 mod 3 = -1 (sign follows DIVIDEND)

Python's % follows the sign of the DIVISOR.
SMT-LIB's mod follows the sign of the DIVIDEND (or is always non-negative).

  -7 % 3:  Python = 2,   SMT mod = -1 (or 2 depending on SMT-LIB version)
  7 % -3:  Python = -2,  SMT mod = 1
  -7 % -3: Python = -1,  SMT mod = -1
"""


def python_mod(a: int, b: int) -> int:
    return a % b


def main() -> None:
    # Positive % positive: same in both
    assert python_mod(7, 3) == 1

    # Negative dividend, positive divisor: DIVERGES
    # CPython: -7 % 3 = 2 (sign follows divisor: positive)
    # SMT: -7 mod 3 = -1 or 2 (implementation-dependent)
    assert python_mod(-7, 3) == 2

    # Positive dividend, negative divisor: DIVERGES
    # CPython: 7 % -3 = -2 (sign follows divisor: negative)
    # SMT: 7 mod -3 = 1 (always non-negative in some SMT-LIB)
    assert python_mod(7, -3) == -2

    # Both negative:
    # CPython: -7 % -3 = -1 (sign follows divisor: negative)
    assert python_mod(-7, -3) == -1

    # Key invariant: a == (a // b) * b + (a % b)
    assert -7 == (-7 // 3) * 3 + (-7 % 3)   # -7 == -4*3 + 2 ✓
    assert 7 == (7 // -3) * -3 + (7 % -3)   # 7 == -4*-3 + (-2) ✓

    print(python_mod(-7, 3), python_mod(7, -3), python_mod(-7, -3))


main()
