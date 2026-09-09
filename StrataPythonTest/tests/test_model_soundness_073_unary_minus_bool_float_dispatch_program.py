# Unary minus (`-x`) missing dispatch for `from_float` and `from_bool` — falls
# to Hole or wrong type tag
"""
Unary minus (`-x`) must dispatch on the tag of x:
- from_int(n) → from_int(-n)
- from_float(f) → from_float(-f)
- from_bool(b) → from_int(-1) if b is True, from_int(0) if False

The model's PNeg likely only handles from_int. It may fall to Hole for
from_float and from_bool, or return the wrong type tag for booleans.
"""


def negate_int(x: int) -> int:
    return -x


def negate_float(x: float) -> float:
    return -x


def negate_bool_as_int(b: bool) -> int:
    # -True == -1, -False == 0 (bool promotes to int under negation)
    return -b


def absolute_value(x: int) -> int:
    if x < 0:
        return -x
    return x


def reflect_point(x: float, y: float) -> tuple[float, float]:
    return (-x, -y)


def main() -> None:
    # Int negation
    assert negate_int(5) == -5
    assert negate_int(-3) == 3
    assert negate_int(0) == 0

    # Float negation
    assert negate_float(3.14) == -3.14
    assert negate_float(-2.5) == 2.5

    # Bool negation: result is int, not bool
    assert negate_bool_as_int(True) == -1
    assert negate_bool_as_int(False) == 0
    assert type(negate_bool_as_int(True)) == int  # NOT bool

    # Absolute value uses negation
    assert absolute_value(5) == 5
    assert absolute_value(-7) == 7

    # Double negation
    x: int = 42
    assert -(-x) == x

    print(negate_int(5), negate_float(3.14), negate_bool_as_int(True))


main()
