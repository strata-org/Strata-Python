# Function called twice — each call must produce fresh symbolic result; shared
# variable would alias the results
"""
FUNCTION CALLED TWICE — RESULTS MUST BE INDEPENDENT

CPython: a = f(x); b = f(x) — two calls, two independent results.
         For PURE functions: a == b (same input → same output).
         For functions with state: a may != b.

Model:   Under value semantics, function calls are pure.
         f(x) called twice should return the SAME value both times
         (if f is deterministic and has no side effects).

         The model must ensure:
         1. Two calls to same function with same args produce same result
            (or at least: each result independently satisfies the return type)
         2. The results are independent values (modifying one doesn't affect other)

This tests that the inter-procedural contract (finding 225) works
correctly when the same function is called multiple times.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


def make_point(n: int) -> Point:
    """Pure factory: same input → same output."""
    return Point(n, n * 2)


def double(x: int) -> int:
    return x * 2


def two_calls_same_result(n: int) -> bool:
    """Two calls with same arg — results should be equal."""
    a: Point = make_point(n)
    b: Point = make_point(n)
    # Pure function: a == b (structural equality for @dataclass)
    return a == b


def two_calls_independent(n: int) -> bool:
    """Two calls — modifying one result doesn't affect other."""
    a: Point = make_point(n)
    b: Point = make_point(n)
    # Create modified version of a
    a2: Point = Point(a.x + 100, a.y)
    # b must be unchanged
    return b.x == n and a2.x == n + 100


def accumulate_calls(xs: list[int]) -> int:
    """Multiple calls in loop — each independent."""
    total: int = 0
    for x in xs:
        total += double(x)
    return total


def calls_in_expression(a: int, b: int) -> int:
    """Two calls in same expression."""
    return double(a) + double(b)


def main() -> None:
    # Test 1: same result for same input
    assert two_calls_same_result(5)

    # Test 2: results are independent
    assert two_calls_independent(3)

    # Test 3: accumulate
    assert accumulate_calls([1, 2, 3]) == 12  # 2+4+6

    # Test 4: two calls in expression
    assert calls_in_expression(3, 4) == 14  # 6+8

    # Test 5: different inputs → different results
    p1: Point = make_point(1)
    p2: Point = make_point(2)
    assert p1.x == 1 and p2.x == 2
    assert p1 != p2

    print("all passed")


main()
