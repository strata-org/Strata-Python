# `float()` conversion from int — `float(5)` must return `from_float(5.0)`; no
# model like finding 017
"""
`float(x)` converts int to float. This is IN (builtin conversion).
The model must handle `float(from_int(n))` → `from_float(to_real(n))`.
If `float()` has no model (like `int()` in finding 017), the result
is Hole.
"""


def int_to_float(x: int) -> float:
    return float(x)


def average(values: list[int]) -> float:
    total: int = 0
    for v in values:
        total = total + v
    return float(total) / float(len(values))


def normalize(x: int, max_val: int) -> float:
    return float(x) / float(max_val)


def main() -> None:
    # Basic conversion
    assert int_to_float(5) == 5.0
    assert int_to_float(0) == 0.0
    assert int_to_float(-3) == -3.0

    # Average using float conversion
    avg: float = average([1, 2, 3, 4, 5])
    assert avg == 3.0

    # Normalize
    n: float = normalize(3, 10)
    assert n == 0.3

    # float(bool)
    assert float(True) == 1.0
    assert float(False) == 0.0

    print(int_to_float(42), average([2, 4, 6]))


main()
