# `x in range(a, b)` membership test — no range-as-container model; desugar to
# `a <= x < b` arithmetic
"""
`x in range(a, b)` membership test — no model for range containment.

In CPython, `x in range(a, b)` is O(1) — it checks:
  a <= x < b and (x - a) % step == 0

This is NOT iteration. CPython's range object has __contains__ that
does arithmetic, not linear search.

The model likely has no representation for range objects at all.
`range(a, b)` is only used in `for i in range(...)` loops, where it's
desugared to a counter. But `x in range(a, b)` as a MEMBERSHIP TEST
(outside a for loop) has no translation.

This is distinct from:
- Finding 045/161 (range iteration semantics in for loops)
- Finding 305 (range(len(lst)) index axiom)

This finding tests range as a CONTAINER for `in` operator.

Uses ONLY confirmed-accepted constructs: range, in, int, bool.
"""


def in_simple_range(x: int) -> bool:
    """x in range(10) checks 0 <= x < 10."""
    return x in range(10)
    # CPython: True for 0..9, False otherwise
    # Model: no range-as-container model → Hole or wrong


def in_range_start_stop(x: int, a: int, b: int) -> bool:
    """x in range(a, b) checks a <= x < b."""
    return x in range(a, b)
    # CPython: True iff a <= x < b
    # Model: Hole


def in_range_with_step(x: int) -> bool:
    """x in range(0, 10, 2) checks x is even and in [0,10)."""
    return x in range(0, 10, 2)
    # CPython: True for 0, 2, 4, 6, 8
    # Model: Hole


def range_membership_as_guard(x: int) -> str:
    """Using range membership as a bounds check."""
    if x in range(1, 101):
        return "valid"
    return "out of range"
    # CPython: "valid" for 1..100
    # Model: condition is Hole → non-deterministic


def equivalent_to_comparison(x: int, lo: int, hi: int) -> bool:
    """x in range(lo, hi) == (lo <= x < hi) for step=1."""
    via_range: bool = x in range(lo, hi)
    via_comparison: bool = lo <= x and x < hi
    return via_range == via_comparison
    # CPython: always True (for step=1)
    # Model: via_range is Hole, comparison is unknown


def main() -> None:
    assert in_simple_range(5) == True
    assert in_simple_range(10) == False
    assert in_simple_range(-1) == False
    assert in_range_start_stop(5, 3, 8) == True
    assert in_range_start_stop(8, 3, 8) == False  # exclusive end
    assert in_range_with_step(4) == True
    assert in_range_with_step(5) == False
    assert range_membership_as_guard(50) == "valid"
    assert range_membership_as_guard(0) == "out of range"
    assert equivalent_to_comparison(5, 1, 10) == True
