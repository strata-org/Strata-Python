# `int + float` → Hole — PAdd has no `(from_int, from_float)` case; CPython
# returns `from_float(4.5)`, model returns Hole
"""
CPython: 3 + 1.5 → 4.5 (float)
Model:   PAdd(from_int(3), from_float(1.5)) → Hole (no int×float case)

The RETURN TYPE is wrong: CPython returns a float, model returns nothing.
"""


def int_plus_float(a: int, b: float) -> float:
    return a + b


def main() -> None:
    # CPython: 3 + 1.5 = 4.5 (type: float)
    result: float = int_plus_float(3, 1.5)
    assert result == 4.5
    # Model: PAdd(from_int(3), from_float(1.5)) has no matching case → Hole
    # Hole is not from_float(4.5) — divergence

    # More examples:
    assert int_plus_float(0, 0.0) == 0.0
    assert int_plus_float(1, -0.5) == 0.5
    assert abs(int_plus_float(-2, 3.7) - 1.7) < 0.0001

    print(result)


main()
