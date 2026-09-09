# `int(float)` truncates toward zero — `int(-2.7)`=-2 not -3; model may use
# floor (wrong direction) or Hole
"""
int(float) truncates toward zero, NOT floor.

In CPython, `int(x)` on a float truncates toward zero:
  int(2.7)  →  2   (toward zero, same as floor for positive)
  int(-2.7) → -2   (toward zero, NOT -3 which is floor)
  int(3.9)  →  3
  int(-3.9) → -3   (NOT -4)

This is DIFFERENT from floor division `//`:
  -7 // 2 = -4  (floor toward -∞)
  int(-7 / 2) = int(-3.5) = -3  (truncate toward 0)

The Laurel model's `to_int_any` (finding 017 notes it's undefined/Hole).
If it IS defined, it must use truncation toward zero (C's `(int)` cast
semantics), NOT floor. If the model reuses the floor-division logic
(which itself has issues per finding 273), it will compute wrong values
for negative floats.

math.trunc() is the explicit form: int(x) == math.trunc(x) for floats.

Uses ONLY confirmed-accepted constructs: int(), float, comparison, arithmetic.
"""


def int_positive_float() -> int:
    """int() on positive float truncates (same as floor)."""
    x: float = 2.7
    result: int = int(x)
    # CPython: 2
    # Model (if Hole): unprovable
    # Model (if floor): 2 (happens to be correct for positive)
    return result


def int_negative_float() -> int:
    """int() on negative float truncates toward zero (NOT floor)."""
    x: float = -2.7
    result: int = int(x)
    # CPython: -2 (truncate toward zero)
    # Model (if floor): -3 — WRONG
    # Model (if Hole): unprovable
    return result


def int_negative_large() -> int:
    """Another negative case to confirm direction."""
    x: float = -9.99
    result: int = int(x)
    # CPython: -9 (toward zero)
    # Model (if floor): -10 — WRONG
    return result


def int_vs_floor_div() -> bool:
    """Demonstrate int() != // for negative values."""
    a: float = -7.0
    b: float = 2.0
    via_int: int = int(a / b)       # int(-3.5) = -3
    via_floor: int = int(a // b)    # int(-4.0) = -4
    # CPython: via_int=-3, via_floor=-4, they differ
    # Model must distinguish these two operations
    return via_int != via_floor  # True in CPython


def truncation_symmetry(x: float) -> bool:
    """int(x) and int(-x) have opposite signs (symmetric around 0)."""
    pos: int = int(x)
    neg: int = int(-x)
    # For x=2.7: int(2.7)=2, int(-2.7)=-2 → 2 == -(-2) ✓
    # Floor would give: floor(2.7)=2, floor(-2.7)=-3 → 2 != -(-3)=3 ✗
    return pos == -neg


def main() -> None:
    assert int_positive_float() == 2
    assert int_negative_float() == -2
    assert int_negative_large() == -9
    assert int_vs_floor_div() == True
    assert truncation_symmetry(2.7) == True
    assert truncation_symmetry(9.99) == True
