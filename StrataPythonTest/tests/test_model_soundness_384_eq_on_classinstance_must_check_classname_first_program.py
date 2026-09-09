# PEq on ClassInstance must check classname FIRST — without it, `Point(1,2) ==
# Vector(1,2)` returns True (WRONG, over-proves)
"""
PEq ON from_ClassInstance MUST CHECK CLASSNAME FIRST

CPython: @dataclass __eq__ checks type(other) is type(self) FIRST.
         Point(1,2) == Vector(1,2) → False (different class!)
         Point(1,2) == Point(1,2) → True (same class, same fields)

Model:   PEq(from_ClassInstance(n1, a1), from_ClassInstance(n2, a2))
         If implemented as: structural_eq(a1, a2)
         → WRONG: ignores classname, says Point == Vector if fields match

         Must be: n1 == n2 AND structural_eq(a1, a2)
         → classname check FIRST, then field comparison

Finding 327 identified this for unrelated classes.
This finding tests the SPECIFIC failure mode: two @dataclass classes
with IDENTICAL field names and values but different classnames.
"""
from dataclasses import dataclass


@dataclass
class Point2D:
    x: int
    y: int


@dataclass
class Vector2D:
    x: int
    y: int


@dataclass
class Size:
    x: int
    y: int


def same_class_equal() -> bool:
    """Same class, same fields → equal."""
    return Point2D(1, 2) == Point2D(1, 2)


def different_class_not_equal() -> bool:
    """Different class, same fields → NOT equal."""
    p: Point2D = Point2D(3, 4)
    v: Vector2D = Vector2D(3, 4)
    # CPython: False (different __class__)
    # Model without classname check: True (same attrs!) — WRONG
    return p != v


def three_classes_same_fields() -> bool:
    """Three different classes, all with x=1, y=2."""
    p: Point2D = Point2D(1, 2)
    v: Vector2D = Vector2D(1, 2)
    s: Size = Size(1, 2)
    # None of these should be equal to each other
    return p != v and p != s and v != s


def equality_in_list(points: list[Point2D], target: Point2D) -> bool:
    """Search uses == which must respect classname."""
    return target in points


def main() -> None:
    # Test 1: same class equality
    assert same_class_equal()

    # Test 2: different class, same fields → NOT equal
    assert different_class_not_equal()

    # Test 3: three classes
    assert three_classes_same_fields()

    # Test 4: list search respects class
    points: list[Point2D] = [Point2D(1, 1), Point2D(2, 2)]
    assert equality_in_list(points, Point2D(2, 2))
    # Vector2D(2,2) should NOT be found in list of Point2D
    # (In CPython this would be False; type mismatch in __eq__)

    # Test 5: same class, different fields → not equal
    assert Point2D(1, 2) != Point2D(1, 3)

    print("all passed")


main()
