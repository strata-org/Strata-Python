# Reflected dispatch: `int + float` — int.__add__(float)→NotImplemented,
# float.__radd__(int)→5.5; model → Hole
"""
MISSING REFLECTED METHOD DISPATCH: int + float

CPython protocol:
  1. int.__add__(float) → NotImplemented
  2. float.__radd__(int) → float result ✓

Model: PAdd(from_int(2), from_float(3.5))
  → match: no (from_int, from_float) case
  → Hole

CPython result: 5.5
Model result:  Hole
"""


def int_plus_float(a: int, b: float) -> float:
    return a + b


def main() -> None:
    # CPython: 2 + 3.5 = 5.5 (via float.__radd__)
    assert int_plus_float(2, 3.5) == 5.5
    assert int_plus_float(0, 1.0) == 1.0
    assert int_plus_float(-1, 0.5) == -0.5

    print(int_plus_float(2, 3.5))


main()
