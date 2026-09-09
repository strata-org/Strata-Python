# `from_float` uses exact `Real` not IEEE 754 — model OVER-PROVES:
# `0.1+0.2==0.3` verified but fails at runtime (false positive)
"""
`from_float(as_float: real)` uses SMT-LIB `Real` (exact rational/real
arithmetic), not IEEE 754 double-precision floating point.

Finding 042 identified `0.1 + 0.2 == 0.3` (True in model, False in CPython).
This finding focuses on DIVISION specifically, where the divergence is
most dangerous for verification:

- `1.0 / 3.0` in CPython: 0.3333333333333333 (rounded)
- `1.0 / 3.0` in model: exactly 1/3 (no rounding)
- `(1.0 / 3.0) * 3.0` in CPython: 1.0 (lucky rounding)
- `(1.0 / 3.0) * 3.0` in model: exactly 1.0 (exact arithmetic)

But:
- `1.0 / 10.0 * 10.0` in CPython: 1.0 (happens to round correctly)
- `0.1 * 3.0` in CPython: 0.30000000000000004 (NOT 0.3)
- `0.1 * 3.0` in model: exactly 0.3

The model OVER-PROVES: it says equalities hold that CPython violates.
This is UNSOUND in the "false verification" direction — the model says
"this assertion passes" but CPython would fail it.

Uses ONLY confirmed-accepted constructs: float, arithmetic, comparison.
"""


def divide_and_multiply(a: float, b: float) -> float:
    """a / b * b should equal a in exact arithmetic, but not in IEEE 754."""
    return (a / b) * b


def sum_tenths() -> float:
    """Sum 0.1 ten times. Exact: 1.0. IEEE 754: 0.9999999999999999."""
    total: float = 0.0
    i: int = 0
    while i < 10:
        total = total + 0.1
        i = i + 1
    return total


def float_equality_trap() -> bool:
    """Model says True (exact reals). CPython says False (IEEE 754)."""
    x: float = 0.1 + 0.2
    return x == 0.3  # False in CPython! True in model!


def division_remainder() -> float:
    """1.0 / 3.0 * 3.0 — happens to be 1.0 in both, but for different reasons."""
    return (1.0 / 3.0) * 3.0


def safe_comparison(a: float, b: float, epsilon: float) -> bool:
    """Correct pattern: compare with tolerance."""
    diff: float = a - b
    if diff < 0.0:
        diff = -diff
    return diff < epsilon


def main() -> None:
    # Division and multiply back — exact in model, approximate in CPython
    # For most values, CPython gets close enough
    assert abs(divide_and_multiply(10.0, 3.0) - 10.0) < 0.0001

    # Sum of 0.1 ten times
    total: float = sum_tenths()
    # In CPython: total is approximately 0.9999999999999999, NOT exactly 1.0
    # In model: total is exactly 1.0
    # We use approximate comparison:
    assert abs(total - 1.0) < 0.0001

    # The dangerous case: exact equality on floats
    # float_equality_trap() returns False in CPython, True in model
    # We just demonstrate the value:
    x: float = 0.1 + 0.2
    # x is 0.30000000000000004 in CPython, 0.3 in model

    # Safe comparison with epsilon
    assert safe_comparison(0.1 + 0.2, 0.3, 0.001) == True

    # Division remainder
    assert abs(division_remainder() - 1.0) < 0.0001

    print(divide_and_multiply(10.0, 3.0), sum_tenths(),
          safe_comparison(0.1 + 0.2, 0.3, 0.001))


main()
