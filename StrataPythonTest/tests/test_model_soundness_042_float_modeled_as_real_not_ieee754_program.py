# `from_float` uses SMT-LIB `Real` (exact reals), not IEEE 754 — `0.1 + 0.2 ==
# 0.3` is True in model, False in CPython
"""
Python floats are IEEE 754 double-precision. The Laurel encoding models
them as mathematical reals (SMT-LIB 'Real' sort). This causes divergence
on any computation where IEEE 754 rounding produces a different result
than exact real arithmetic.

Classic example: 0.1 + 0.2 != 0.3 in IEEE 754, but == 0.3 in reals.
"""


def check_sum(a: float, b: float, expected: float) -> bool:
    return a + b == expected


def main() -> None:
    # IEEE 754: 0.1 + 0.2 = 0.30000000000000004 (not exactly 0.3)
    # Real arithmetic: 0.1 + 0.2 = 0.3 (exact)
    result: bool = check_sum(0.1, 0.2, 0.3)
    print(result)  # CPython: False, Laurel: True

    # More examples of IEEE 754 rounding divergence:
    r2: bool = 0.1 * 3.0 == 0.3
    print(r2)  # CPython: False, Laurel: True

    r3: bool = 1.1 + 2.2 == 3.3
    print(r3)  # CPython: False, Laurel: True

    # This one happens to be exact in IEEE 754:
    r4: bool = 1.0 + 2.0 == 3.0
    print(r4)  # CPython: True, Laurel: True (agrees here)


main()
