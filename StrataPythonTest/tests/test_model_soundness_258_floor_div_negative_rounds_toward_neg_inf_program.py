# `//` negative rounds toward -∞ — CPython: `-7//2 = -4`; SMT `div`: `-7 div 2
# = -3`; model computes WRONG VALUE
"""
CPython: -7 // 2 → -4 (floor toward negative infinity)
Model:   PFloorDiv uses SMT `div` → -7 div 2 = -3 (truncation toward zero)

Python's // rounds toward NEGATIVE INFINITY.
SMT-LIB's div rounds toward ZERO (Euclidean/truncation).

These differ for negative operands:
  -7 // 2:  Python = -4 (floor),  SMT = -3 (truncate)
  7 // -2:  Python = -4 (floor),  SMT = -3 (truncate)
  -7 // -2: Python = 3 (floor),   SMT = 3 (truncate) — same!
"""


def floor_div_neg_num(a: int, b: int) -> int:
    return a // b


def main() -> None:
    # Positive // positive: same in both
    assert floor_div_neg_num(7, 2) == 3

    # Negative numerator: DIVERGES
    # CPython: -7 // 2 = -4 (floor toward -inf)
    # SMT div: -7 div 2 = -3 (truncate toward 0)
    assert floor_div_neg_num(-7, 2) == -4

    # Negative denominator: DIVERGES
    # CPython: 7 // -2 = -4
    # SMT div: 7 div -2 = -3
    assert floor_div_neg_num(7, -2) == -4

    # Both negative: SAME (floor and truncate agree)
    assert floor_div_neg_num(-7, -2) == 3

    # More cases:
    assert floor_div_neg_num(-1, 2) == -1   # SMT would give 0
    assert floor_div_neg_num(-10, 3) == -4  # SMT would give -3
    assert floor_div_neg_num(10, -3) == -4  # SMT would give -3

    print(floor_div_neg_num(-7, 2), floor_div_neg_num(7, -2),
          floor_div_neg_num(-1, 2))


main()
