# Reflected dispatch: `int / float` — int.__truediv__(float)→NotImplemented,
# float.__rtruediv__(int)→2.5; model → Hole
"""
MISSING REFLECTED METHOD DISPATCH: int / float

CPython protocol:
  1. int.__truediv__(float) → NotImplemented
  2. float.__rtruediv__(int) → float result ✓

Model: PTrueDiv(from_int(10), from_float(4.0))
  → match: no (from_int, from_float) case
  → Hole

CPython result: 2.5
Model result:  Hole
"""


def int_div_float(a: int, b: float) -> float:
    return a / b


def float_div_int(a: float, b: int) -> float:
    return a / b


def main() -> None:
    # CPython: 10 / 4.0 = 2.5 (via float.__rtruediv__)
    assert int_div_float(10, 4.0) == 2.5
    assert int_div_float(1, 0.5) == 2.0

    # CPython: 7.5 / 3 = 2.5 (via float.__truediv__)
    assert float_div_int(7.5, 3) == 2.5

    print(int_div_float(10, 4.0), float_div_int(7.5, 3))


main()
