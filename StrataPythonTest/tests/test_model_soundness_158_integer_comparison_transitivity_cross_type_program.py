# Cross-type comparison transitivity — int/float comparison requires coercion
# to common Real sort; without it, transitive reasoning breaks
"""
Python allows comparing int and float freely: `3 == 3.0` is True,
`2 < 2.5` is True. The model must handle cross-type comparisons
correctly, including TRANSITIVITY:

  If a == b and b == c, then a == c.
  If a < b and b < c, then a < c.

When the model uses separate tags (from_int vs from_float), cross-type
comparison requires coercion. If PEq/PLt only handle same-tag pairs
(finding 076), then transitivity through mixed types breaks:

  x: int = 3
  y: float = 3.0
  z: int = 3

  x == y → True (cross-type)
  y == z → True (cross-type)
  x == z → True (same-type)

But if cross-type comparison falls to Hole, the solver cannot prove
that x == z follows from x == y and y == z.

More critically: ordering chains like `a < b < c` where types differ.

Uses ONLY confirmed-accepted constructs: int, float, comparison, function def.
"""


def int_equals_float(a: int, b: float) -> bool:
    return a == b


def float_less_than_int(a: float, b: int) -> bool:
    return a < b


def transitivity_eq(x: int, y: float, z: int) -> bool:
    # If x == y and y == z, then x == z must hold
    if x == y and y == z:
        return x == z
    return True  # vacuously true if premise fails


def transitivity_lt(a: int, b: float, c: int) -> bool:
    # If a < b and b < c, then a < c must hold
    if a < b and b < c:
        return a < c
    return True


def mixed_chain_comparison(x: int, y: float, z: int) -> bool:
    # x < y < z should work with mixed types
    # Desugars to: x < y and y < z
    if x < y and y < z:
        return x < z  # must be provable from the two premises
    return True


def clamp_float_to_int_bounds(val: float, lo: int, hi: int) -> float:
    # Common pattern: compare float against int bounds
    if val < lo:
        return float(lo)
    if val > hi:
        return float(hi)
    return val


def main() -> None:
    # Basic cross-type equality
    assert int_equals_float(3, 3.0) == True
    assert int_equals_float(3, 3.1) == False
    assert int_equals_float(0, 0.0) == True

    # Cross-type ordering
    assert float_less_than_int(2.5, 3) == True
    assert float_less_than_int(3.5, 3) == False
    assert float_less_than_int(3.0, 3) == False  # equal, not less

    # Transitivity of equality through float
    assert transitivity_eq(3, 3.0, 3) == True
    assert transitivity_eq(0, 0.0, 0) == True

    # Transitivity of ordering through float
    assert transitivity_lt(1, 2.5, 4) == True
    assert transitivity_lt(1, 1.5, 2) == True

    # Mixed chain
    assert mixed_chain_comparison(1, 2.5, 4) == True

    # Clamp
    assert clamp_float_to_int_bounds(5.5, 0, 10) == 5.5
    assert clamp_float_to_int_bounds(-1.0, 0, 10) == 0.0
    assert clamp_float_to_int_bounds(15.0, 0, 10) == 10.0

    print(int_equals_float(3, 3.0), float_less_than_int(2.5, 3),
          transitivity_eq(3, 3.0, 3))


main()
