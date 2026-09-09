# `abs()` on float/int has no model — `abs(-3.14)` returns Hole; trivial
# `ite(x>=0, x, -x)` definition missing
"""
abs() on float has no model — abs(-3.14) returns Hole.

Finding 026/228 note that abs() has no Laurel model. This finding
specifically demonstrates abs() on FLOAT values, where the model
must return from_float (not from_int), and the semantics are trivial:
  abs(x) = x if x >= 0 else -x

The fix is a simple conditional, but without it:
- abs(-3.14) → Hole (unconstrained value)
- Downstream comparisons like `abs(x) >= 0` are unprovable
- Guard patterns like `if abs(x - y) < epsilon:` can't be verified

Uses ONLY confirmed-accepted constructs: abs, float, int, comparison.
"""


def abs_positive_float(x: float) -> float:
    """abs of positive float is identity."""
    return abs(x)
    # CPython with x=3.14: 3.14
    # Model: Hole


def abs_negative_float(x: float) -> float:
    """abs of negative float negates."""
    return abs(x)
    # CPython with x=-3.14: 3.14
    # Model: Hole


def abs_negative_int(x: int) -> int:
    """abs of negative int."""
    return abs(x)
    # CPython with x=-5: 5
    # Model: Hole


def abs_always_nonneg(x: float) -> bool:
    """abs(x) >= 0 is always True — unprovable without model."""
    return abs(x) >= 0.0
    # CPython: always True
    # Model: Hole >= 0.0 → unknown


def distance(a: float, b: float) -> float:
    """Absolute difference — common pattern."""
    return abs(a - b)
    # CPython: always non-negative
    # Model: Hole


def within_epsilon(a: float, b: float, eps: float) -> bool:
    """Float comparison with tolerance — requires abs model."""
    return abs(a - b) < eps
    # CPython with a=1.0, b=1.001, eps=0.01: True
    # Model: Hole < eps → unknown


def main() -> None:
    assert abs_positive_float(3.14) == 3.14
    assert abs_negative_float(-3.14) == 3.14
    assert abs_negative_int(-5) == 5
    assert abs_always_nonneg(3.14) == True
    assert abs_always_nonneg(-3.14) == True
    assert abs_always_nonneg(0.0) == True
    assert within_epsilon(1.0, 1.001, 0.01) == True
    assert within_epsilon(1.0, 2.0, 0.01) == False
