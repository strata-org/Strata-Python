# Comparison chain desugaring — `a < b < c` requires PLt to return from_bool
# AND cross-type cases to work AND and/or to handle bools
"""
Chained comparisons `a < b < c` desugar to `a < b and b < c` with b
evaluated ONCE. Each comparison returns a bool. The `and` combines them.

Under tag-based dispatch:
1. PLt(a, b) must return from_bool (not from_int or Hole)
2. PLt(b, c) must return from_bool
3. The `and` must operate on from_bool values

If PLt returns the wrong tag (e.g., from_int(1) for True), the `and`
operation may fail (finding 056: and/or on non-bool).

If PLt returns Hole for a valid pair (finding 201), the chain breaks.

Finding 066 identified evaluation-once semantics. This finding focuses
on the TAG CORRECTNESS of comparison results flowing into boolean ops.

Uses ONLY confirmed-accepted constructs: int, float, comparison, and.
"""


def in_range(x: int, lo: int, hi: int) -> bool:
    """Chained comparison: lo <= x < hi."""
    return lo <= x and x < hi


def three_way(a: int, b: int, c: int) -> bool:
    """a < b < c — both comparisons must be bool."""
    return a < b and b < c


def mixed_type_chain(a: int, b: float, c: int) -> bool:
    """Cross-type chain: int < float < int."""
    return a < b and b < c


def comparison_result_is_bool() -> bool:
    """Verify comparison returns bool, not int."""
    result: bool = 3 < 5  # must be from_bool(True), not from_int(1)
    return result  # True


def comparison_in_arithmetic() -> int:
    """Using comparison result in arithmetic (bool is int)."""
    # (3 < 5) is True, True + True = 2
    a: bool = 3 < 5
    b: bool = 10 > 2
    return a + b  # True + True = 2 (bool arithmetic, finding 166)


def chained_with_equality(a: int, b: int, c: int) -> bool:
    """a <= b <= c includes equality."""
    return a <= b and b <= c


def main() -> None:
    # Range check
    assert in_range(5, 0, 10) == True
    assert in_range(10, 0, 10) == False  # exclusive upper
    assert in_range(-1, 0, 10) == False

    # Three-way
    assert three_way(1, 2, 3) == True
    assert three_way(1, 3, 2) == False
    assert three_way(2, 2, 3) == False  # not strict <

    # Mixed type
    assert mixed_type_chain(1, 2.5, 4) == True
    assert mixed_type_chain(3, 2.5, 4) == False

    # Bool result
    assert comparison_result_is_bool() == True

    # Comparison in arithmetic
    assert comparison_in_arithmetic() == 2

    # Chained with equality
    assert chained_with_equality(1, 2, 3) == True
    assert chained_with_equality(1, 1, 1) == True  # all equal

    print(in_range(5, 0, 10), three_way(1, 2, 3),
          mixed_type_chain(1, 2.5, 4))


main()
