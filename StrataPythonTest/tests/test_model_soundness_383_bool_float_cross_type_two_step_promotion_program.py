# Bool × float arithmetic — two-step promotion (bool→int→float) needed; no
# `(from_bool, from_float)` case exists
"""
BOOL × FLOAT CROSS-TYPE — TWO-STEP PROMOTION NEEDED

CPython: True + 1.5 → 2.5 (float)
         bool → int → float (two promotions!)

         Step 1: True → 1 (bool is subclass of int)
         Step 2: 1 + 1.5 → 2.5 (int promoted to float for arithmetic)

Model:   PAdd(from_bool(True), from_float(1.5))
         Tag dispatch has cases for:
         - (from_int, from_int) → from_int
         - (from_float, from_float) → from_float
         - (from_int, from_float) → from_float (if finding 282 fixed)
         - (from_bool, from_int) → ??? (if finding 166 fixed)

         But (from_bool, from_float) has NO case even if the above are fixed.
         It requires TWO promotions: bool→int→float.
         The model must either:
         1. Add explicit (from_bool, from_float) cases for all operators
         2. Normalize from_bool to from_int BEFORE dispatch (finding 166)

Finding 166 proposes normalizing bool→int. But even with that fix,
the COMBINATION bool×float requires the int×float case to also exist.
This tests the FULL CHAIN: bool → int → float.
"""


def bool_plus_float(b: bool, f: float) -> float:
    """bool + float → float (two-step promotion)."""
    return b + f


def bool_times_float(b: bool, f: float) -> float:
    """bool * float → float."""
    return b * f


def bool_minus_float(b: bool, f: float) -> float:
    """bool - float → float."""
    return b - f


def float_minus_bool(f: float, b: bool) -> float:
    """float - bool → float (asymmetric!)."""
    return f - b


def bool_in_mixed_expression(flag: bool, x: float, y: float) -> float:
    """Common pattern: bool as coefficient in float expression."""
    # flag * x + (not flag) * y — conditional without branching
    # Requires: bool * float → float
    return flag * x


def main() -> None:
    # Test 1: True + 1.5 = 2.5
    assert bool_plus_float(True, 1.5) == 2.5
    assert bool_plus_float(False, 1.5) == 1.5

    # Test 2: True * 3.14 = 3.14
    assert bool_times_float(True, 3.14) == 3.14
    assert bool_times_float(False, 3.14) == 0.0

    # Test 3: True - 0.5 = 0.5
    assert bool_minus_float(True, 0.5) == 0.5
    assert bool_minus_float(False, 0.5) == -0.5

    # Test 4: asymmetric — 2.5 - True = 1.5
    assert float_minus_bool(2.5, True) == 1.5
    assert float_minus_bool(2.5, False) == 2.5

    # Test 5: bool as coefficient
    assert bool_in_mixed_expression(True, 10.0, 20.0) == 10.0
    assert bool_in_mixed_expression(False, 10.0, 20.0) == 0.0

    print("all passed")


main()
