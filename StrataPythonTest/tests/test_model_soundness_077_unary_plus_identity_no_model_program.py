# Unary plus (`+x`) has no model — identity for int/float but promotes bool to
# int; may be silently dropped
"""
Unary `+x` is the identity operator for numeric types: it returns the
value unchanged but as a new object. For int and float, `+x == x`.
For bool, `+True == 1` (promotes to int, like all arithmetic on bool).

The model likely has no PPos (unary plus) operator at all, since it
seems like a no-op. But it's a real operator that:
1. Validates the operand is numeric (raises TypeError on str/list/None)
2. Promotes bool to int
"""


def identity_int(x: int) -> int:
    return +x


def identity_float(x: float) -> float:
    return +x


def promote_bool(b: bool) -> int:
    # +True == 1, +False == 0 (result is int, not bool)
    return +b


def double_positive(x: int) -> int:
    # Unary + is sometimes used for emphasis/clarity
    return +(+x)


def main() -> None:
    # Int: identity
    assert identity_int(5) == 5
    assert identity_int(-3) == -3
    assert identity_int(0) == 0

    # Float: identity
    assert identity_float(3.14) == 3.14
    assert identity_float(-2.5) == -2.5

    # Bool: promotes to int
    assert promote_bool(True) == 1
    assert promote_bool(False) == 0
    assert type(+True) == int  # NOT bool

    # Double application
    assert double_positive(42) == 42

    # Combined with negation
    x: int = 7
    assert +x == -(-x)

    print(identity_int(5), identity_float(3.14), promote_bool(True))


main()
