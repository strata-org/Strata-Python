# Chained comparison `1 < x < 10` — must desugar to `(1<x) and (x<10)` with
# single eval of x; wrong desugar gives Hole
"""
CHAINED COMPARISON — MIDDLE OPERAND EVALUATED ONCE

CPython: 1 < x < 10 desugars to: (1 < x) and (x < 10)
         with x evaluated ONCE (not twice).

         For pure expressions this doesn't matter.
         But the RESULT must be from_bool (not from_int).
         And the short-circuit must work: if 1 < x is False,
         x < 10 is NOT evaluated.

Model:   Finding 066 identified that middle operands may be evaluated twice.
         Finding 202 identified that PLt must return from_bool for chaining.

         The concrete issue: `1 < x < 10` must:
         1. Compute PLt(1, x) → from_bool(True/False)
         2. If False: short-circuit, return from_bool(False)
         3. If True: compute PLt(x, 10) → from_bool(True/False)
         4. Return the AND of both

         If the model evaluates as PLt(PLt(1, x), 10):
         → PLt(from_bool(True), 10) → comparing bool to int → Hole!

CPython result: True (for x=5)
Model result: Hole (if desugared wrong)
"""


def in_range(x: int, lo: int, hi: int) -> bool:
    """Chained comparison: lo < x < hi."""
    return lo < x < hi


def in_range_inclusive(x: int, lo: int, hi: int) -> bool:
    """Chained: lo <= x <= hi."""
    return lo <= x <= hi


def three_way(a: int, b: int, c: int) -> bool:
    """Three-way chain: a < b < c."""
    return a < b < c


def mixed_comparison(x: int) -> bool:
    """Mixed operators in chain: 0 <= x < 100."""
    return 0 <= x < 100


def main() -> None:
    # Test 1: basic range check
    assert in_range(5, 1, 10)
    assert not in_range(0, 1, 10)
    assert not in_range(10, 1, 10)  # exclusive

    # Test 2: inclusive range
    assert in_range_inclusive(5, 1, 10)
    assert in_range_inclusive(1, 1, 10)  # inclusive
    assert in_range_inclusive(10, 1, 10)  # inclusive
    assert not in_range_inclusive(0, 1, 10)

    # Test 3: three-way
    assert three_way(1, 2, 3)
    assert not three_way(1, 3, 2)
    assert not three_way(2, 1, 3)

    # Test 4: mixed operators
    assert mixed_comparison(0)
    assert mixed_comparison(50)
    assert not mixed_comparison(-1)
    assert not mixed_comparison(100)

    print("all passed")


main()
