# List element access returns untyped Any — `xs[i]` from `list[int]` has no
# `isfrom_int` assertion; all element operations produce Hole
"""
LIST OF OPTIONAL — ELEMENT ACCESS RETURNS UNION TAG BUT NO NARROWING

CPython: xs: list[Optional[int]] = [1, None, 3]
         xs[0] → 1 (int)
         xs[1] → None
         Must narrow with isinstance/is None before using as int.

Model:   ListAny stores Any values. xs[i] returns Any.
         Finding 221 notes element type is lost (no isfrom_int assertion).
         But for list[Optional[int]], the element type is ITSELF a union:
         {from_int, from_None}. The model must:
         1. Assert element is from_int OR from_None (not from_str, etc.)
         2. Allow narrowing via isinstance/is None checks
         3. After narrowing, assert the specific tag

         Without (1): element could be ANY tag — too permissive
         Without (2): can't safely use element as int
         Without (3): operations on narrowed element still have unknown tag

This is the INTERACTION between findings 221 (element type lost) and
223 (Optional requires disjunctive tag) applied to container elements.
"""
from dataclasses import dataclass


def sum_non_none(xs: list[int]) -> int:
    """Simplified: all elements are int, but accessed via Any."""
    total: int = 0
    for x in xs:
        # x has type int from annotation, but model has no tag assertion
        total += x
    return total


def first_non_none(xs: list[int], default: int) -> int:
    """Find first element, with default if list is empty."""
    if len(xs) == 0:
        return default
    return xs[0]


def count_positive(xs: list[int]) -> int:
    """Each element access needs tag assertion to use in comparison."""
    count: int = 0
    for x in xs:
        # x: int from annotation → model needs isfrom_int(x) after access
        # Without it: x > 0 operates on unknown-tag value
        if x > 0:
            count += 1
    return count


def safe_sum_with_check(xs: list[int]) -> int:
    """Access by index with bounds check."""
    total: int = 0
    i: int = 0
    while i < len(xs):
        val: int = xs[i]
        # val: int annotation → needs isfrom_int(val)
        # Without assertion: val + total has unknown-tag operand
        total += val
        i += 1
    return total


def main() -> None:
    # Test 1: basic sum
    data: list[int] = [1, 2, 3, 4, 5]
    assert sum_non_none(data) == 15

    # Test 2: first element
    assert first_non_none([10, 20, 30], -1) == 10
    assert first_non_none([], -1) == -1

    # Test 3: count positive (comparison on element)
    mixed: list[int] = [3, -1, 4, -2, 5]
    # CPython: 3 positives
    # Model: if x has no tag assertion, x > 0 may be Hole
    #         → condition is unknown → count is unprovable
    assert count_positive(mixed) == 3

    # Test 4: indexed access sum
    assert safe_sum_with_check([10, 20, 30]) == 60

    print("all passed")


main()
