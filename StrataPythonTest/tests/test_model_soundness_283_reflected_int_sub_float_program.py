# Reflected dispatch: `int - float` — int.__sub__(float)→NotImplemented,
# float.__rsub__(int)→7.5; model → Hole
"""
MISSING REFLECTED METHOD DISPATCH: int - float

CPython protocol:
  1. int.__sub__(float) → NotImplemented
  2. float.__rsub__(int) → float result ✓

Model: PSub(from_int(10), from_float(2.5))
  → match: no (from_int, from_float) case
  → Hole

CPython result: 7.5
Model result:  Hole
"""


def int_minus_float(a: int, b: float) -> float:
    return a - b


def float_minus_int(a: float, b: int) -> float:
    return a - b


def main() -> None:
    # CPython: 10 - 2.5 = 7.5 (via float.__rsub__)
    assert int_minus_float(10, 2.5) == 7.5
    assert int_minus_float(0, 1.0) == -1.0

    # CPython: 5.5 - 2 = 3.5 (via float.__sub__ directly)
    assert float_minus_int(5.5, 2) == 3.5

    print(int_minus_float(10, 2.5), float_minus_int(5.5, 2))


main()
