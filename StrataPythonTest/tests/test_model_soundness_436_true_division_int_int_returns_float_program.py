# `7 / 2` → `3.5` (float); model returns Hole or from_int(3); true division
# ALWAYS returns from_float
"""
TRUE DIVISION int / int ALWAYS RETURNS float

DIVERGENCE:
  CPython:  7 / 2  → 3.5  (type: float)
  Model:    PTrueDiv(from_int(7), from_int(2)) → Hole or from_int(3)

  CPython:  6 / 2  → 3.0  (type: float, even when "evenly divisible")
  Model:    PTrueDiv(from_int(6), from_int(2)) → Hole or from_int(3)

The return TYPE is always float in CPython. The model either:
- Has no PTrueDiv at all → Hole
- Uses PFloorDiv (wrong value: 3 instead of 3.5)
- Returns from_int (wrong tag: should be from_float)
"""


def true_div(a: int, b: int) -> float:
    return a / b


def average(xs: list[int]) -> float:
    """Common pattern: sum / len gives float."""
    total: int = 0
    for x in xs:
        total += x
    return total / len(xs)


def main() -> None:
    # CPython: 7 / 2 = 3.5 (float)
    # Model: Hole or 3 (int) — WRONG
    assert true_div(7, 2) == 3.5

    # CPython: 6 / 2 = 3.0 (float, NOT int 3!)
    # Model: may return from_int(3) — wrong tag
    assert true_div(6, 2) == 3.0
    assert isinstance(6 / 2, float)  # ALWAYS float

    # CPython: 1 / 3 = 0.333...
    assert abs(true_div(1, 3) - 0.3333333) < 0.001

    # Average
    assert average([2, 4, 6]) == 4.0
    assert abs(average([1, 2, 3, 4]) - 2.5) < 0.001

    print("all passed")


main()
