# Function postcondition not assumed at call site — return value is
# unconstrained; caller can't prove properties of result without
# inlining/contracts
"""
When function `f` has return type `-> int` and the caller does:
    x: int = f(args)
    assert x > 0  # should be provable if f's postcondition guarantees it

The model must ASSUME the function's postcondition at the call site.
Without this, the caller knows nothing about the return value — it's
an unconstrained value of the correct type.

Key issue: inter-procedural reasoning. If `f` is verified to always
return a positive int, the caller of `f` must be able to USE that fact.

Two approaches:
1. Inline f's body (only works for non-recursive, small functions)
2. Use f's contract (postcondition) as an assumption at the call site

If neither is done, the return value is Hole (unconstrained), and the
caller cannot prove anything about it.

Uses ONLY confirmed-accepted constructs: function def, int, assert.
"""


def absolute_value(x: int) -> int:
    if x >= 0:
        return x
    return -x


def always_positive(x: int) -> int:
    """Returns x if positive, else 1."""
    if x > 0:
        return x
    return 1


def double(x: int) -> int:
    return x * 2


def caller_uses_postcondition() -> int:
    val: int = always_positive(42)
    # val > 0 should be provable from always_positive's body
    assert val > 0
    return val


def caller_uses_arithmetic_postcondition(n: int) -> int:
    d: int = double(n)
    # d == 2*n should be provable
    assert d == n * 2
    return d


def chained_calls(x: int) -> int:
    a: int = absolute_value(x)
    # a >= 0 should be provable
    b: int = always_positive(a)
    # b > 0 should be provable
    return a + b


def caller_needs_abs_nonneg(x: int) -> bool:
    result: int = absolute_value(x)
    # This MUST be provable: absolute_value always returns >= 0
    return result >= 0


def main() -> None:
    assert caller_uses_postcondition() == 42
    assert caller_uses_arithmetic_postcondition(5) == 10
    # abs(3) = 3, always_positive(3) = 3 (since 3 > 0), so 3+3 = 6
    assert chained_calls(3) == 6
    # abs(-4)=4, always_positive(4)=4, 4+4=8
    assert chained_calls(-4) == 8
    assert caller_needs_abs_nonneg(5) == True
    assert caller_needs_abs_nonneg(-5) == True
    assert caller_needs_abs_nonneg(0) == True

    print(caller_uses_postcondition(),
          caller_uses_arithmetic_postcondition(5),
          caller_needs_abs_nonneg(-7))


main()
