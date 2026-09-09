# Ordering comparison on @dataclass raises TypeError — `Point(1,2) <
# Point(3,4)` crashes; model returns Hole not exception
"""
Ordering comparison (<, >, <=, >=) on @dataclass instances raises TypeError.

In CPython, @dataclass (without order=True) does NOT generate __lt__,
__gt__, __le__, __ge__. Attempting `Point(1,2) < Point(3,4)` raises:
  TypeError: '<' not supported between instances of 'Point' and 'Point'

The Laurel model's PLt/PGt/PLe/PGe dispatch on from_ClassInstance likely
falls to the catch-all case. Per finding 270/286/290, the catch-all
should produce exception(TypeError), but if it produces Hole instead,
the model silently accepts code that WILL crash at runtime.

This is distinct from:
- Finding 111 (operators on ClassInstance produce no error — covers +,-,*,/)
- Finding 290 (missing exception for str < int)

This finding specifically tests ORDERING comparisons on @dataclass objects,
which is a common mistake (forgetting order=True or using @dataclass
without @total_ordering).

Uses ONLY confirmed-accepted constructs: @dataclass, comparison operators, if.
"""
from dataclasses import dataclass


@dataclass
class Point:
    x: int
    y: int


@dataclass
class Temperature:
    celsius: float


def compare_points_lt(a: Point, b: Point) -> bool:
    """Point < Point raises TypeError in CPython."""
    # CPython: TypeError: '<' not supported between instances of 'Point' and 'Point'
    # Model (Hole catch-all): returns some unconstrained value — UNSOUND
    # Model (exception catch-all): returns exception(TypeError) — correct
    return a < b  # type: ignore


def compare_points_gt(a: Point, b: Point) -> bool:
    """Point > Point also raises TypeError."""
    return a > b  # type: ignore


def compare_points_le(a: Point, b: Point) -> bool:
    """Point <= Point also raises TypeError."""
    return a <= b  # type: ignore


def sort_by_comparison(p1: Point, p2: Point) -> Point:
    """Using comparison in if-condition — crashes at runtime."""
    if p1 < p2:  # type: ignore
        return p1
    else:
        return p2
    # CPython: TypeError on the if-condition evaluation
    # Model: may take either branch (Hole in condition → non-deterministic)


def compare_temperatures(a: Temperature, b: Temperature) -> bool:
    """Same issue with any @dataclass without order=True."""
    return a < b  # type: ignore


def equality_works_but_ordering_doesnt(a: Point, b: Point) -> bool:
    """== works (dataclass generates __eq__), but < does not."""
    eq_ok: bool = a == b  # This is fine — __eq__ is generated
    # lt_fails: bool = a < b  # This would crash
    return eq_ok


def main() -> None:
    p1: Point = Point(x=1, y=2)
    p2: Point = Point(x=3, y=4)

    # Equality works fine
    assert equality_works_but_ordering_doesnt(p1, p2) == False
    assert equality_works_but_ordering_doesnt(p1, Point(x=1, y=2)) == True

    # These ALL raise TypeError in CPython:
    try:
        compare_points_lt(p1, p2)
        assert False  # should not reach here
    except TypeError:
        pass  # expected

    try:
        sort_by_comparison(p1, p2)
        assert False
    except TypeError:
        pass  # expected
