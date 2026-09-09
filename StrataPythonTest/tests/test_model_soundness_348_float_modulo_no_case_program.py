# Float modulo `%` — PMod has no `(from_float, from_float)` case; `7.5 % 2.0`
# returns Hole; sign-of-divisor rule needed
"""
FLOAT MODULO — PMod HAS NO (from_float, from_float) CASE

CPython: 7.5 % 2.0 → 1.5 (float modulo is well-defined)
         -7.5 % 2.0 → 0.5 (sign follows divisor, same as int)
         3.5 % 1.0 → 0.5

Model:   PMod likely only handles (from_int, from_int) → SMT mod.
         (from_float, from_float) has no case → Hole.
         Even if it existed, SMT Real mod semantics differ from Python's.

The subset declares % as IN for float×float (frontend-subset.md: "Binary
arithmetic: +, -, *, //, %, **. Supported for int×int→int, float×float→float").
But the model has no implementation for float modulo.
"""


def float_mod_basic(a: float, b: float) -> float:
    return a % b


def float_mod_negative(a: float, b: float) -> float:
    """Python float % follows same sign-of-divisor rule as int %."""
    return a % b


def is_half_integer(x: float) -> bool:
    """Common pattern: check if float has .5 fractional part."""
    return x % 1.0 == 0.5


def normalize_angle(degrees: float) -> float:
    """Normalize angle to [0, 360) range using modulo."""
    return degrees % 360.0


def main() -> None:
    # Test 1: basic float modulo
    # CPython: 7.5 % 2.0 = 1.5
    # Model: PMod(from_float(7.5), from_float(2.0)) → Hole (no float case)
    assert float_mod_basic(7.5, 2.0) == 1.5

    # Test 2: float mod with result 0
    assert float_mod_basic(4.0, 2.0) == 0.0

    # Test 3: negative dividend (sign follows divisor)
    # CPython: -7.5 % 2.0 = 0.5 (not -1.5!)
    # Same sign rule as int: result has sign of divisor
    result: float = float_mod_negative(-7.5, 2.0)
    assert abs(result - 0.5) < 0.0001

    # Test 4: negative divisor
    # CPython: 7.5 % -2.0 = -0.5
    result2: float = float_mod_negative(7.5, -2.0)
    assert abs(result2 - (-0.5)) < 0.0001

    # Test 5: practical pattern — half-integer check
    assert is_half_integer(3.5)
    assert is_half_integer(0.5)
    assert not is_half_integer(3.0)
    assert not is_half_integer(3.7)

    # Test 6: angle normalization
    assert normalize_angle(450.0) == 90.0
    assert normalize_angle(-90.0) == 270.0
    assert normalize_angle(0.0) == 0.0

    print("all passed")


main()
