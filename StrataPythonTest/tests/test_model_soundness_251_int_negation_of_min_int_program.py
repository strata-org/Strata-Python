# Unary negation PNeg must be defined — if uninterpreted, `-x` is Hole; must
# map to SMT `(- n)` for int; handle float/bool too
"""
CPython: -(-5) == 5 (negation of negative is positive)
Model: PNeg(from_int(n)) should return from_int(-n).
       But if PNeg only handles from_int and not from_bool/from_float,
       negating a bool or float falls to Hole.

More critically: the model uses SMT-LIB Int which has no overflow.
-x is always well-defined. But if PNeg is UNINTERPRETED (no definition),
then -5 returns Hole instead of from_int(-5).

CPython result: -5 == from_int(-5)
Model result: PNeg(from_int(5)) == Hole (if uninterpreted)

Finding 073 identified missing float/bool dispatch. This finding tests
that BASIC int negation works and that double-negation is identity.
"""


def negate(x: int) -> int:
    return -x


def double_negate(x: int) -> int:
    return -(-x)  # must equal x


def negate_zero() -> int:
    return -0  # must be 0


def abs_via_negate(x: int) -> int:
    if x < 0:
        return -x
    return x


def difference(a: int, b: int) -> int:
    """a - b == a + (-b)."""
    return a + (-b)


def negate_in_expression(x: int, y: int) -> int:
    """Negation as part of larger expression."""
    return -x + y  # (-x) + y


def main() -> None:
    assert negate(5) == -5
    assert negate(-3) == 3
    assert negate(0) == 0

    assert double_negate(7) == 7
    assert double_negate(-4) == -4

    assert negate_zero() == 0

    assert abs_via_negate(-10) == 10
    assert abs_via_negate(10) == 10

    assert difference(10, 3) == 7
    assert difference(3, 10) == -7

    assert negate_in_expression(3, 10) == 7

    print(negate(5), double_negate(7), abs_via_negate(-10))


main()
